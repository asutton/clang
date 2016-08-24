//===--- SemaExprCXX.cpp - Semantic Analysis for Expressions --------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief Implements semantic analysis for C++ expressions.
///
//===----------------------------------------------------------------------===//

#include "clang/Sema/SemaInternal.h"
#include "TreeTransform.h"
#include "TypeLocBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/PartialDiagnostic.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/DeclSpec.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Lookup.h"
#include "clang/Sema/ParsedTemplate.h"
#include "clang/Sema/Scope.h"
#include "clang/Sema/ScopeInfo.h"
#include "clang/Sema/Template.h"
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/PointerSumType.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/ErrorHandling.h"
using namespace clang;
using namespace sema;

// The expression '$x' returns an object describing the reflected entity.
// The type of that object depends on the type of the thing reflected.
//
// The Id argument is not null.
ExprResult
Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, Expr* E)
{
  if (isa<TypoExpr>(E)) {
    ExprResult Fixed = CorrectDelayedTyposInExpr(E);
    if (!Fixed.isUsable())
      return ExprError();
    E = Fixed.get();
  }

  // TODO: Handle the case where Id is dependent (type? value?). We
  // just want to return a dependent expression that we can substitute
  // into later.
  if (E->isTypeDependent() || E->isValueDependent()) {
    E->dump();
    return ExprError(Diag(OpLoc, diag::err_not_implemented));
  }

  if (OverloadExpr* Ovl = dyn_cast<OverloadExpr>(E)) {
    // FIXME: This should be okay. We should be able to provide a limited
    // interface to overloaded functions.
    return ExprError(Diag(OpLoc, diag::err_reflected_overload)
                     << Ovl->getSourceRange());
  }

  if (!isa<DeclRefExpr>(E))
    llvm_unreachable("Expression reflection not implemented");

  // For non-dependent expressions, the result of reflection depends
  // on the kind of entity.
  ValueDecl* Value = cast<DeclRefExpr>(E)->getDecl();
  if (VarDecl* Var = dyn_cast<VarDecl>(Value))
    return BuildVariableReflection(OpLoc, Var);
  if (FunctionDecl* Fn = dyn_cast<FunctionDecl>(Value))
    return BuildFunctionReflection(OpLoc, Fn);
  if (EnumConstantDecl* Enum = dyn_cast<EnumConstantDecl>(Value))
    return BuildEnumeratorReflection(OpLoc, Enum);

  llvm_unreachable("Unhandled reflected declaration");
}

ExprResult
Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, Declarator& D)
{
  TypeSourceInfo *TI = GetTypeForDeclarator(D, CurScope);
  QualType QT = TI->getType();
  
  return IntegerLiteral::Create(Context, 
                                Context.MakeIntValue(0, Context.IntTy), 
                                Context.IntTy, OpLoc);
}

ExprResult
Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, CXXScopeSpec& SS, 
                          IdentifierInfo* II, SourceLocation IdLoc)
{
  // Perform a lookup in the current scope for II to determine if
  // it refers to a namespace.
  LookupResult R(*this, II, OpLoc, LookupNamespaceName);
  LookupParsedName(R, CurScope, &SS);
  if (!R.isSingleResult())
    return ExprError();  
  NamespaceDecl* NS = R.getAsSingle<NamespaceDecl>();
  if (!NS)
    return ExprError();

  return IntegerLiteral::Create(Context, 
                                Context.MakeIntValue(0, Context.IntTy), 
                                Context.IntTy, OpLoc);
}


// Used to encode the kind of entity reflected. This value is packed into
// the low order bits of each reflected pointer. Because we stuff pointer
// values, all must be aligned at 2 bytes (which is generally guaranteed).
//
// TODO: Could we safely use high order bits?
enum ReflectionKind {
  RK_Decl = 1,
  RK_Type = 2,
  RK_Expr = 3
};

using ReflectionValue = llvm::PointerSumType<
  ReflectionKind,
  llvm::PointerSumTypeMember<RK_Decl, Decl *>,
  llvm::PointerSumTypeMember<RK_Type, Type *>,
  llvm::PointerSumTypeMember<RK_Expr, Expr *>
>;


static std::pair<ReflectionKind, void*> ExplodeOpaqueValue(std::uintptr_t N) {
  // Look away. I'm totally breaking abstraction.
  using Helper = llvm::detail::PointerSumTypeHelper<
    ReflectionKind,
    llvm::PointerSumTypeMember<RK_Decl, Decl *>,
    llvm::PointerSumTypeMember<RK_Type, Type *>,
    llvm::PointerSumTypeMember<RK_Expr, Expr *>
  >;
  ReflectionKind K = (ReflectionKind)(N & Helper::TagMask);
  void* P = (void*)(N & Helper::PointerMask);
  return {K, P};
}


// Returns a constructed temporary aggregate describing the declaration D.
// 
// When building reflections in non-dependent contexts, we don't maintain 
// the expression as a new kind of AST node. Instead, we directly produce 
// a temporary if the expression had been `Type { args... }`. The alternative 
// would be to produce a new AST node denoting temporary. However, that would
// require special handling in all cases.
//
// In dependent code, we absolutely must produce the a new AST node. That
// would resolve to an type construction expression during substitution.
// 
// NOTE: If we want to reflect the names of declarations, we need to
// create string literals at reasonable points in the program. These may
// need to become implicit global or local variables (like __func__).
// Note that we only need to generate these if we request the name
// property.
//
// TODO: This assumes that all reflections have the same internal structure.
// If they don't, which will probably happen at some point, then we'll
// need to push this code down into the other Build* functions.
ExprResult
Sema::BuildDeclarationReflection(SourceLocation Loc, ValueDecl* D, 
                                 char const* K) {
  // Get the wrapper type.
  ClassTemplateDecl* Temp = RequireReflectionType(Loc, K);
  if (!Temp)
    return ExprError();
  TemplateName TempName(Temp);

  // Build a template specialization, instantiate it, and then complete it.
  QualType IntPtrTy = Context.getIntPtrType();
  ReflectionValue RV = ReflectionValue::create<RK_Decl>(D);
  llvm::APSInt IntPtrVal = Context.MakeIntValue(RV.getOpaqueValue(), IntPtrTy);

  TemplateArgument Arg(Context, IntPtrVal, IntPtrTy);
  TemplateArgumentLoc ArgLoc(Arg, TemplateArgumentLocInfo());
  TemplateArgumentListInfo TempArgs(Loc, Loc);
  TempArgs.addArgument(ArgLoc);
  QualType TempType = CheckTemplateIdType(TempName, Loc, TempArgs);
  if (RequireCompleteType(Loc, TempType, diag::err_incomplete_type))
    assert(false && "Failed to instantiate reflection type");

  // Produce a value-initialized temporary of the required type.
  SmallVector<Expr*, 1> Args;
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(TempType);
  InitializationKind Kind = InitializationKind::CreateValue(Loc, Loc, Loc);
  InitializationSequence InitSeq(*this, Entity, Kind, Args);
  return InitSeq.Perform(*this, Entity, Kind, Args);
}

ExprResult
Sema::BuildVariableReflection(SourceLocation Loc, VarDecl* Var) {
  return BuildDeclarationReflection(Loc, Var, "variable");
}

ExprResult
Sema::BuildFunctionReflection(SourceLocation Loc, FunctionDecl* Fn) {
  return BuildDeclarationReflection(Loc, Fn, "function");
}

ExprResult
Sema::BuildEnumeratorReflection(SourceLocation Loc, EnumConstantDecl* Enum) {
  return BuildDeclarationReflection(Loc, Enum, "enumerator");
}


// TODO: Build a class corresponding to the most-derived kind.
//
// TODO: Accommodate cv-qualifiers somewhow. Perhaps add them as template
// parameters a la:
//
//    template<reflection_t X, bool C, bool V>
//    struct type { ... };
//
// Note that we would need a few alternative traits to combine cv information
// in order to accurately get the type name. I also suspect that we'll need
// noexcept information for function types, and possibly more state flags
// for other types beyond this. Same idea. X is always the value type. 
// Additional flags can be added as extensions.
//
// TODO: There's a lot of duplication between this and the BuildDeclReflection
// function above. Surely we can simplify.
//
ExprResult
Sema::BuildTypeReflection(SourceLocation Loc, QualType QT) {  
  // Get the wrapper type.
  ClassTemplateDecl* Temp = RequireReflectionType(Loc, "type");
  if (!Temp)
    return ExprError();
  TemplateName TempName(Temp);

  Type* T = const_cast<Type*>(QT.getTypePtr());
  ReflectionValue RV = ReflectionValue::create<RK_Type>(T);

  // Build a template specialization, instantiate it, and then complete it.
  QualType IntPtrTy = Context.getIntPtrType();
  llvm::APSInt IntPtrVal = Context.MakeIntValue(RV.getOpaqueValue(), IntPtrTy);
  TemplateArgument Arg(Context, IntPtrVal, IntPtrTy);
  TemplateArgumentLoc ArgLoc(Arg, TemplateArgumentLocInfo());
  TemplateArgumentListInfo TempArgs(Loc, Loc);
  TempArgs.addArgument(ArgLoc);
  QualType TempType = CheckTemplateIdType(TempName, Loc, TempArgs);
  if (RequireCompleteType(Loc, TempType, diag::err_incomplete_type))
    assert(false && "Failed to instantiate reflection type");

  // Produce a value-initialized temporary of the required type.
  SmallVector<Expr*, 1> Args;
  InitializedEntity Entity = InitializedEntity::InitializeTemporary(TempType);
  InitializationKind Kind = InitializationKind::CreateValue(Loc, Loc, Loc);
  InitializationSequence InitSeq(*this, Entity, Kind, Args);
  return InitSeq.Perform(*this, Entity, Kind, Args);
}


// Returns the cpp3k namespace if a suitable header has been included. If not, 
// a diagnostic is emitted, and nullptr is returned.
//
// TODO: We should probably cache this the same way that we do
// with typeid (see CXXTypeInfoDecl in Sema.h).
NamespaceDecl*
Sema::RequireCpp3kNamespace(SourceLocation Loc) {
  IdentifierInfo *Cpp3kII = &PP.getIdentifierTable().get("cpp3k");
  LookupResult R(*this, Cpp3kII, Loc, LookupNamespaceName);
  LookupQualifiedName(R, Context.getTranslationUnitDecl());
  if (!R.isSingleResult()) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  NamespaceDecl* Cpp3k = R.getAsSingle<NamespaceDecl>();
  assert(Cpp3k && "cpp3k is not a namespace");
  return Cpp3k;
}

// As above, but requires cpp3k::meta.
NamespaceDecl*
Sema::RequireCpp3kMetaNamespace(SourceLocation Loc) {
  NamespaceDecl* Cpp3k = RequireCpp3kNamespace(Loc);
  if (!Cpp3k)
    return nullptr;

  // Get the cpp3k::meta namespace.
  IdentifierInfo *MetaII = &PP.getIdentifierTable().get("meta");
  LookupResult R(*this, MetaII, Loc, LookupNamespaceName);
  LookupQualifiedName(R, Cpp3k);
  if (!R.isSingleResult()) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  NamespaceDecl* Meta = R.getAsSingle<NamespaceDecl>();
  assert(Meta && "cpp3k::meta is not a namespace");
  return Meta;
}

// Returns the class with the given name in the std::[experimental::]meta
// namespaace. If no such class can be found, a diagnostic is emitted,
// and nullptr returned.
//
// TODO: Cache these types so we don't keep doing lookup. In on the first
// lookup, cache the names of ALL meta types so that we can easily check
// for appropriate arguments in the reflection traits.
ClassTemplateDecl*
Sema::RequireReflectionType(SourceLocation Loc, char const* Name) {
  NamespaceDecl* Meta = RequireCpp3kMetaNamespace(Loc);
  if (!Meta)
    return nullptr;

  // Get the corresponding reflection class.
  IdentifierInfo *TypeII = &PP.getIdentifierTable().get(Name);
  LookupResult R(*this, TypeII, SourceLocation(), LookupAnyName);
  LookupQualifiedName(R, Meta);
  ClassTemplateDecl* Decl = R.getAsSingle<ClassTemplateDecl>();
  if (!Decl) {
    Diag(Loc, diag::err_need_header_before_dollar);
    return nullptr;
  }
  return Decl;
}

// Information supporting reflection operations.
//
// TODO: Move all of the functions below into this class since it provides
// the context for their evaluation.
struct Reflector
{
  Sema& S;
  SourceLocation KWLoc;
  SourceLocation RParenLoc;
  ArrayRef<Expr *> Args;
  ArrayRef<llvm::APSInt> Vals;

  ExprResult Reflect(ReflectionTrait RT, Decl* D);
  ExprResult Reflect(ReflectionTrait RT, Type* T);

  ExprResult ReflectName(Decl* D);
  ExprResult ReflectName(Type* D);
  
  ExprResult ReflectQualifiedName(Decl* D);
  ExprResult ReflectQualifiedName(Type* D);
  
  ExprResult ReflectLinkage(Decl* D);
  ExprResult ReflectVariableStorage(VarDecl* D);
  ExprResult ReflectFunctionStorage(FunctionDecl* D);
  ExprResult ReflectStorage(Decl* D);
  ExprResult ReflectType(Decl* D);
  ExprResult ReflectNumParameters(Decl* D);
  ExprResult ReflectParameter(Decl* D, const llvm::APSInt& N);
};


ExprResult Sema::ActOnReflectionTrait(SourceLocation KWLoc,
                                      ReflectionTrait Kind, 
                                      ArrayRef<Expr *> Args,
                                      SourceLocation RParenLoc) {
  // If any arguments are dependent, then the result is a dependent
  // expression.
  //
  // TODO: What if a argument is type dependent? Or instantiation dependent?
  for (unsigned i = 0; i < Args.size(); ++i) {
    if (Args[i]->isValueDependent()) {
      QualType Ty = Context.DependentTy;
      return new (Context) ReflectionTraitExpr(Context, Kind, Ty, Args, 
                                               APValue(), KWLoc, RParenLoc);
    }
  }

  // Ensure that each operand has integral type.
  for (unsigned i = 0; i < Args.size(); ++i) {
    Expr* E = Args[i];
    if (!E->getType()->isIntegerType()) {
      Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
      return ExprError();
    }
  }

  // Evaluate all of the operands ahead of time. Note that trait arity
  // is checked at parse time.
  SmallVector<llvm::APSInt, 2> Vals;
  Vals.resize(Args.size());
  for (unsigned i = 0; i < Args.size(); ++i) {
    Expr* E = Args[i];
    if (!E->EvaluateAsInt(Vals[i], Context)) {
      Diag(E->getLocStart(), diag::err_expr_not_ice) << 1;
      return ExprError();
    }
  }

  // FIXME: Verify that this is actually a reflected node.
  std::pair<ReflectionKind, void*> Info = 
      ExplodeOpaqueValue(Vals[0].getExtValue());

  Reflector R {*this, KWLoc, RParenLoc, Args, Vals};
  if (Info.first == RK_Decl)
    return R.Reflect(Kind, (Decl*)Info.second);
  if (Info.first == RK_Type)
    return R.Reflect(Kind, (Type*)Info.second);

  llvm_unreachable("Unhandled reflection");
}

// Returns a string literal having the given name.
static ExprResult MakeString(ASTContext& C, const std::string &Str)
{
  llvm::APSInt Size = C.MakeIntValue(Str.size() + 1, C.getSizeType());
  QualType Elem = C.getConstType(C.CharTy);
  QualType Type = C.getConstantArrayType(Elem, Size, ArrayType::Normal, 0);
  return StringLiteral::Create(C, Str, StringLiteral::Ascii, false, Type, 
                               SourceLocation());
}


ExprResult Reflector::Reflect(ReflectionTrait RT, Decl* D) {
  switch (RT) {
  case URT_GetName:
    return ReflectName(D);
  case URT_GetQualifiedName:
    return ReflectQualifiedName(D);
  case URT_GetLinkage:
    return ReflectLinkage(D);
  case URT_GetStorage:
    return ReflectStorage(D);
  case URT_GetType:
    return ReflectType(D);
  case URT_GetNumParameters:
    return ReflectNumParameters(D);
  case BRT_GetParameter:
    assert(Vals.size() == 2 && "Wrong arity");
    return ReflectParameter(D, Vals[1]);
  }

  // FIXME: Improve this error message.
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}


ExprResult Reflector::Reflect(ReflectionTrait RT, Type* T) {
  switch (RT) {
  case URT_GetName:
    return ReflectName(T);
  case URT_GetQualifiedName:
    return ReflectQualifiedName(T);
  default:
    break;
  }

  // FIXME: Improve this error message.
  S.Diag(KWLoc, diag::err_reflection_not_supported);
  return ExprError();
}

// Returns a named declaration or emits an error and returns nullptr.
static NamedDecl* RequireNamedDecl(Reflector R, Decl* D) {
  Sema& S = R.S;
  if (!isa<NamedDecl>(D)) {
    S.Diag(R.Args[0]->getLocStart(), diag::err_reflection_not_named);
    return nullptr;
  }
  return cast<NamedDecl>(D); 
}

ExprResult Reflector::ReflectName(Decl* D) {
  if (NamedDecl* ND = RequireNamedDecl(*this, D))
    return MakeString(S.Context, ND->getNameAsString());  
  return ExprError();
}

ExprResult Reflector::ReflectQualifiedName(Decl* D) {
  if (NamedDecl* ND = RequireNamedDecl(*this, D))
    return MakeString(S.Context, ND->getQualifiedNameAsString());  
  return ExprError();
}

ExprResult Reflector::ReflectName(Type* T) {
  // Use the underlying declaration of tag types for the name. This way,
  // we won't generate "struct or enum" as part of the type.
  if (TagDecl* TD = T->getAsTagDecl())
    return MakeString(S.Context, TD->getNameAsString());
  QualType QT(T, 0);
  return MakeString(S.Context, QT.getAsString());  
}

ExprResult Reflector::ReflectQualifiedName(Type* T) {
  if (TagDecl* TD = T->getAsTagDecl())
    return MakeString(S.Context, TD->getQualifiedNameAsString());
  QualType QT(T, 0);
  return MakeString(S.Context, QT.getAsString());  
}

ExprResult Reflector::ReflectLinkage(Decl* D) { 
  if (NamedDecl* ND = RequireNamedDecl(*this, D)) {
    ASTContext& C = S.Context;
    QualType T = C.IntTy;
    llvm::APSInt N = C.MakeIntValue((int)ND->getFormalLinkage(), T);
    return IntegerLiteral::Create(C, N, T, KWLoc);
  }
  return ExprError();
}

ExprResult Reflector::ReflectVariableStorage(VarDecl* D) {
  ASTContext& C = S.Context;
  QualType T = C.IntTy;
  llvm::APSInt N = C.MakeIntValue((int)D->getStorageClass(), T);
  return IntegerLiteral::Create(C, N, T, KWLoc);
}

ExprResult Reflector::ReflectFunctionStorage(FunctionDecl* D) {
  ASTContext& C = S.Context;
  QualType T = C.IntTy;
  llvm::APSInt N = C.MakeIntValue((int)D->getStorageClass(), T);
  return IntegerLiteral::Create(C, N, T, KWLoc);
}

ExprResult Reflector::ReflectStorage(Decl* D) {
  if (VarDecl* Var = dyn_cast<VarDecl>(D))
    return ReflectVariableStorage(Var);
  if (FunctionDecl* Fn = dyn_cast<FunctionDecl>(D))
    return ReflectFunctionStorage(Fn);

  // FIXME: This is the wrong error message. Should be D does not have
  // a storage class.
  S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_named);
  return ExprError();
}

ExprResult Reflector::ReflectType(Decl* D) {
  if (ValueDecl* VD = dyn_cast<ValueDecl>(D))
    return S.BuildTypeReflection(KWLoc, VD->getType());
  S.Diag(Args[0]->getLocStart(), diag::err_reflection_not_typed);
  return ExprError();
}

static FunctionDecl* RequireFunctionDecl(Reflector R, Decl* D) {
  if (!isa<FunctionDecl>(D)) {
    R.S.Diag(R.Args[0]->getLocStart(), diag::err_reflection_not_function);
    return nullptr;
  }
  return cast<FunctionDecl>(D);
}

ExprResult Reflector::ReflectNumParameters(Decl* D) {
  if (FunctionDecl* Fn = RequireFunctionDecl(*this, D)) {
    ASTContext& C = S.Context;
    QualType T = C.UnsignedIntTy;
    llvm::APSInt N = C.MakeIntValue(Fn->getNumParams(), T);
    return IntegerLiteral::Create(C, N, T, KWLoc);
  }
  return ExprError();
}

ExprResult Reflector::ReflectParameter(Decl* D, const llvm::APSInt& N) {
  if (FunctionDecl* Fn = RequireFunctionDecl(*this, D)) {
    unsigned Num = N.getExtValue();
    if (Num >= Fn->getNumParams()) {
      S.Diag(Args[1]->getLocStart(), diag::err_parameter_out_of_bounds);
      return ExprError();
    }
    ParmVarDecl* Parm = Fn->getParamDecl(Num);
    return S.BuildDeclarationReflection(KWLoc, Parm, "parameter");
  }
  return ExprError();
}


