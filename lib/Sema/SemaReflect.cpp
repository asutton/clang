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
#include "clang/AST/ASTLambda.h"
#include "clang/AST/CXXInheritance.h"
#include "clang/AST/CharUnits.h"
#include "clang/AST/DeclObjC.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprObjC.h"
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
#include "llvm/ADT/STLExtras.h"
#include "llvm/Support/ErrorHandling.h"
using namespace clang;
using namespace sema;

// The expression '$x' returns an object describing the reflected entity.
// The type of that object depends on the type of the thing reflected.
//
// The Id argument is not null.
ExprResult
Sema::ActOnCXXReflectExpr(SourceLocation OpLoc, Expr* Id)
{
  // TODO: Handle the case where Id is dependent (type? value?). We
  // just want to return a dependent expression that we can substitute
  // into later.
  if (Id->isTypeDependent() || Id->isValueDependent())
    return ExprError(Diag(OpLoc, diag::err_not_implemented));

  if (OverloadExpr* Ovl = dyn_cast<OverloadExpr>(Id)) {
    // FIXME: This should be okay. We should be able to provide a limited
    // interface to overloaded functions.
    return ExprError(Diag(OpLoc, diag::err_reflected_overload)
                     << Ovl->getSourceRange());
  }

  // For non-dependent expressions, the result of reflection depends
  // on the kind of entity.
  ValueDecl* Value = cast<DeclRefExpr>(Id)->getDecl();
  if (VarDecl* Var = dyn_cast<VarDecl>(Value))
    return BuildVariableReflection(OpLoc, Var);
  if (FunctionDecl* Fn = dyn_cast<FunctionDecl>(Value))
    return BuildFunctionReflection(OpLoc, Fn);
  if (EnumConstantDecl* Enum = dyn_cast<EnumConstantDecl>(Value))
    return BuildEnumeratorReflection(OpLoc, Enum);

  llvm_unreachable("unhandled reflected declaration");
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
  llvm::APSInt IntPtrVal = Context.MakeIntValue((std::intptr_t)D, IntPtrTy);
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


static ValueDecl*
GetReflectedValueDecl(Sema& S, ASTContext& C, Expr* const& N)
{
  llvm::APSInt IntPtrVal;
  if (!N->EvaluateAsInt(IntPtrVal, C)) {
    S.Diag(N->getLocStart(), diag::err_expr_not_ice);
    return nullptr;
  };
  return (ValueDecl*)(std::intptr_t)IntPtrVal.getExtValue();
}


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


#if 0
  // Get the type and check extra operands to the trait.
  Expr* Arg = nullptr;
  QualType Ty;
  switch (Kind) {
  case URT_GetName:
  case URT_GetQualifiedName:
    // These have const char* type.
    Ty = Context.getPointerType(Context.getConstType(Context.CharTy));
    break;

  case URT_GetLinkage:
  case URT_GetStorage:
    // These have integer type.
    Ty = Context.IntTy;
    break;
  
  case URT_GetNumParameters:
    // These have std::size_t type.
    Ty = Context.getSizeType();
    break;

  case URT_GetType: {
    ValueDecl* D = GetReflectedValueDecl(*this, Context, Node);
    if (!D)
      return ExprError();

    // RecordDecl* RD = RequireReflectionType(KWLoc, "type");
    // if (!RD)
    //   return ExprError();
    // Ty = Context.getTagDeclType(RD);
    // break;
  }

  case BRT_GetParameter: {
    ValueDecl* D = GetReflectedValueDecl(*this, Context, Node);
    if (!D)
      return ExprError();

    Arg = Args[1];
    llvm::APSInt Index;
    if (!Arg->EvaluateAsInt(Index, Context)) {
      Diag(Arg->getLocStart(), diag::err_expr_not_ice);
      return ExprError();
    };

    // FIXME: Fail with a less bad error.
    FunctionDecl* Fn = cast<FunctionDecl>(D);
    ValueDecl* Parm = Fn->getParamDecl(Index.getExtValue());

    // TODO: Do I actually need to instantiate the class or can I just
    // build the type?
    Expr* Expr = BuildDeclarationReflection(KWLoc, Parm, "parameter").get();
    Ty = Expr->getType();
    break;
  }
  }

  if (Ty.isNull())
    llvm_unreachable("Unknown reflection trait");

  if (Args.size() == 1) {
    return new (Context) UnaryReflectionTraitExpr(Kind, KWLoc, Ty, Node);
  } else {
    assert(Arg && "Second argument of binary trait not set");
    return new (Context) BinaryReflectionTraitExpr(Kind, KWLoc, Ty, Node, Arg);
  }
#endif

  return ExprError();  
}


#if 0
// Returns an expression representing the requested attributed.
//
// TODO: Check that this expression can appear only in a function with the 
// __eager specifier.
//
// TODO: Factor out common code for all trait expressions.
ExprResult
Sema::ActOnGetAttributeTraitExpr(SourceLocation Loc, 
                                 ExprResult NodeExpr,
                                 ExprResult AttrExpr)
{
  // TODO: Check some basic properties of the reflection and attribute.
  Expr* Node = NodeExpr.get();
  Expr* Attr = AttrExpr.get();

  // If the selector is value dependent, we can't compute the type.
  // Return an un-evaluated, un-interpreted node.
  if (Attr->isValueDependent()) {
    return new (Context) GetAttributeTraitExpr(Loc, Context.DependentTy,
                                               Node, Attr);
  }

  // Evaluate the attribute selector in order to determine the type
  // of the expression.
  //
  // TODO: Why am I not passing the APSInt directly to the node? It
  // doesn't make sense to keep evaluating this expression, especially
  // when it determines the type.
  llvm::APSInt Result;
  if (!Attr->isIntegerConstantExpr(Result, Context)) {
    Diag(Loc, diag::err_expr_not_ice) << 1 << Attr->getSourceRange();
    return ExprResult();
  }
  QualType Type = GetReflectedAttributeType(Context, Result.getExtValue());
  if (Type.isNull()) {
    Diag(Loc, diag::err_invalid_attribute_id);
    return ExprError();
  }

  // Apply lvalue-to-rvalue conversions.
  Node = DefaultLvalueConversion(Node).get();

  return new (Context) GetAttributeTraitExpr(Loc, Type, Node, Attr);
}

ExprResult
Sema::ActOnGetArrayElementTraitExpr(SourceLocation Loc, 
                                    ExprResult NodeExpr,
                                    ExprResult AttrExpr, 
                                    ExprResult ElemExpr)
{
  Expr* Node = NodeExpr.get();
  Expr* Attr = AttrExpr.get();
  Expr* Elem = ElemExpr.get();

  // If the selector is value dependent, we can't compute the type.
  // Return an un-evaluated, un-interpreted node.
  if (Attr->isValueDependent()) {
    return new (Context) GetArrayElementTraitExpr(Loc, Context.DependentTy,
                                                  Node, Attr, Elem);
  }

  // Evaluate the attribute selector in order to determine the type
  // of the expression.
  //
  // TODO: Why am I not passing the APSInt directly to the node? It
  // doesn't make sense to keep evaluating this expression, especially
  // when it determines the type.
  llvm::APSInt Result;
  if (!Attr->isIntegerConstantExpr(Result, Context)) {
    Diag(Loc, diag::err_expr_not_ice) << 1 << Attr->getSourceRange();
    return ExprResult();
  }
  QualType Type = GetReflectedElementType(*this, Loc, Result.getExtValue());
  if (Type.isNull()) {
    Diag(Loc, diag::err_invalid_attribute_id);
    return ExprError();
  }

  // Apply lvalue-to-rvalue conversions to the other attributes.
  Node = DefaultLvalueConversion(Node).get();
  Elem = DefaultLvalueConversion(Elem).get();

  return new (Context) GetArrayElementTraitExpr(Loc, Type, Node, Attr, Elem);
}
#endif
