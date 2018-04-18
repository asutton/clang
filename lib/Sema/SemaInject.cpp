//===--- SemaInject.cpp - Semantic Analysis for Injection -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file implements semantic rules for the injection of declarations into
//  various declarative contexts.
//
//===----------------------------------------------------------------------===//

#include "TreeTransform.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Sema/Initialization.h"
#include "clang/Sema/Template.h"
#include "clang/Sema/SemaInternal.h"

using namespace clang;
using namespace sema;

InjectionContext::InjectionContext(Sema &SemaRef, 
                                   CXXFragmentDecl *Frag, 
                                   DeclContext *Injectee)
    : SemaRef(SemaRef), Prev(SemaRef.CurrentInjectionContext), 
      Fragment(Frag), Injectee(Injectee) {
  SemaRef.CurrentInjectionContext = this;
}

InjectionContext::~InjectionContext() {
  if (Prev != (InjectionContext *)0x1)
    SemaRef.CurrentInjectionContext = Prev;
}

InjectionContext *InjectionContext::Detach() {
  SemaRef.CurrentInjectionContext = Prev;
  Prev = (InjectionContext *)0x1;
  return this;
}

void InjectionContext::Attach() {
  assert((Prev == (InjectionContext *)0x1) && "Context not detached");
  Prev = SemaRef.CurrentInjectionContext;
  SemaRef.CurrentInjectionContext = this;
}

void InjectionContext::AddDeclSubstitution(Decl *Orig, Decl *New) {
  assert(DeclSubsts.count(Orig) == 0 && "Overwriting substitution");
  DeclSubsts.try_emplace(Orig, New);
}

void InjectionContext::AddPlaceholderSubstitution(Decl *Orig, 
                                                  QualType T, 
                                                  const APValue &V) { 
  assert(isa<VarDecl>(Orig) && "Expected a variable declaration");
  assert(PlaceholderSubsts.count(Orig) == 0 && "Overwriting substitution");
  PlaceholderSubsts.try_emplace(Orig, T, V);
}

void InjectionContext::AddPlaceholderSubstitutions(DeclContext *Fragment,
                                                   CXXRecordDecl *Reflection,
                                                   ArrayRef<APValue> Captures) {
  assert(isa<CXXFragmentDecl>(Fragment) && "Context is not a fragment");
  auto FieldIter = Reflection->field_begin();
  auto PlaceIter = Fragment->decls_begin();
  for (std::size_t I = 0; I < Captures.size(); ++I) {
    Decl *Var = *PlaceIter++;
    QualType Ty = (*FieldIter++)->getType();
    const APValue &Val = Captures[I];
    AddPlaceholderSubstitution(Var, Ty, Val);
  }
}

Decl *InjectionContext::GetDeclReplacement(Decl *D) {
  auto Iter = DeclSubsts.find(D);
  if (Iter != DeclSubsts.end())
    return Iter->second;
  else
    return nullptr;
}

Expr *InjectionContext::GetPlaceholderReplacement(DeclRefExpr *E) {
  auto Iter = PlaceholderSubsts.find(E->getDecl());
  if (Iter != PlaceholderSubsts.end()) {
    // Build a new constant expression as the replacement. The source
    // expression is opaque since the actual declaration isn't part of
    // the output AST (but we might want it as context later -- makes
    // pretty printing more elegant).
    const TypedValue &TV = Iter->second;
    Expr *O = new (SemaRef.Context) OpaqueValueExpr(E->getLocation(), 
                                                    TV.Type, VK_RValue, 
                                                    OK_Ordinary, E);
    return new (SemaRef.Context) CXXConstantExpr(O, TV.Value);
  } else {
    return nullptr;
  }
}

// -------------------------------------------------------------------------- //
// Injection

static inline ASTContext& getASTContext(InjectionContext &Cxt) {
  return Cxt.SemaRef.getASTContext();
}

/// Try to find a replacement for the given declaration.
///
/// FIXME: We really want a resolve or lookup operation. If the declaration
/// cannot be resolved, then we need to lookup the use of the name in the
/// current context.
static Decl* ResolveDecl(InjectionContext &Cxt, Decl *D) {
  // If the original declaration is not in the fragment, then we can simply
  // bind to the original name.
  //
  // NOTE: If the original declaration is captured, then we shouldn't be
  // resolving use this mechanism.
  if (!D->isInFragment())
    return D;
  
  return Cxt.GetDeclReplacement(D);
}

static DeclarationName InjectName(InjectionContext &Cxt, 
                                  const DeclarationName &N);
static NestedNameSpecifierLoc InjectNameSpecifier(InjectionContext &Cxt, 
                                                  const NestedNameSpecifierLoc& NNS,
                                                  Decl *FirstDecl = nullptr);
static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, 
                                          const DeclarationNameInfo& DNI);
static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, NamedDecl *D);

static QualType InjectType(InjectionContext &Cxt, TypeLocBuilder &TLB, TypeLoc TL);
static QualType InjectType(InjectionContext &Cxt, QualType T);
static QualType InjectType(InjectionContext &Cxt, const Type *T);
static TypeSourceInfo *InjectType(InjectionContext &Cxt, TypeSourceInfo *TSI);
static TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, NamedDecl *D);
static TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, DeclaratorDecl *D);

static QualType InjectDeducibleType(InjectionContext &Ext, QualType T);
static TypeSourceInfo *InjectDeducibleType(InjectionContext &Ext, TypeSourceInfo *T);

static StmtResult InjectStmt(InjectionContext &Cxt, Stmt *S);
static StmtResult InjectStmt(InjectionContext &Cxt, StmtResult S);

static ExprResult InjectExpr(InjectionContext &Cxt, Expr *E);
static ExprResult InjectExpr(InjectionContext &Cxt, ExprResult E);
static ExprResult InjectInit(InjectionContext &Cxt, Expr *E, bool NotCopyInit);

static bool InjectExprs(InjectionContext &Cxt, 
                        Expr *const *Args, 
                        unsigned NumArgs, 
                        SmallVectorImpl<Expr *> &Out);
static bool InjectArgs(InjectionContext &Cxt, 
                       Expr *const *Args, 
                       unsigned NumArgs, 
                       SmallVectorImpl<Expr *> &Out);

static Decl *InjectDecl(InjectionContext &Cxt, Decl *D);

// Transform template arguments in the range [First, Last).
template<typename InputIterator>
static bool InjectTemplateArguments(InjectionContext &Cxt, 
                                    InputIterator First, 
                                    InputIterator Last, 
                                    TemplateArgumentListInfo& Output) {
  llvm_unreachable("not implemented");
}

// Transform template arguments in the range [Input, Input + Count).
static bool InjectTemplateArguments(InjectionContext &Cxt, 
                                    const TemplateArgumentLoc *Input, 
                                    unsigned Count,
                                    TemplateArgumentListInfo& Output) {
  return InjectTemplateArguments(Cxt, Input, Input + Count, Output);
}


// FIXME: Implement me. In general, we just need to be sure to apply
// transformations to idexprs. Otherwise, these things don't change too
// much.
static DeclarationName InjectName(InjectionContext &Cxt, 
                                  const DeclarationName &N) {
  return N;
}

// Note that FirstDecl is the first qualifier in scope for certain kinds
// of member declarations. This can be null.
static NestedNameSpecifierLoc InjectNameSpecifier(InjectionContext &Cxt, 
                                                  const NestedNameSpecifierLoc &NNS,
                                                  Decl *FirstDecl) {
  llvm_unreachable("not implemented");
}

/// Returns a transformed version of the declaration name.
static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, 
                                          const DeclarationNameInfo& DNI) {
  assert(DNI.getName() && "Injection of absent name");
  DeclarationName N = InjectName(Cxt, DNI.getName());
  return DeclarationNameInfo(N, DNI.getLoc());  
}

/// Returns a transformed version of the declared name of D.
static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, NamedDecl *D) {
  DeclarationName N = InjectName(Cxt, D->getDeclName());
  return DeclarationNameInfo(N, D->getLocation());  
}

/// Used to implement a number of simple transformation.
template <class TyLoc> 
static inline QualType InjectTypeSpecType(InjectionContext &Cxt,
                                          TypeLocBuilder &TLB, 
                                          TyLoc TL) {
  TyLoc NewTL = TLB.push<TyLoc>(TL.getType());
  NewTL.setNameLoc(TL.getNameLoc());
  return TL.getType();
}

static QualType InjectBuiltinType(InjectionContext &Cxt, 
                                  TypeLocBuilder &TLB, 
                                  BuiltinTypeLoc TL) {
  BuiltinTypeLoc NewTL = TLB.push<BuiltinTypeLoc>(TL.getType());
  NewTL.setBuiltinLoc(TL.getBuiltinLoc());
  if (TL.needsExtraLocalData())
    NewTL.getWrittenBuiltinSpecs() = TL.getWrittenBuiltinSpecs();
  return TL.getType();
}

static QualType InjectComplexType(InjectionContext &Cxt, 
                                  TypeLocBuilder &TLB, 
                                  ComplexTypeLoc TL) {
  return InjectTypeSpecType(Cxt, TLB, TL);
}

static QualType InjectParenType(InjectionContext &Cxt, 
                                TypeLocBuilder &TLB,
                                ParenTypeLoc TL) {
  QualType Inner = InjectType(Cxt, TLB, TL.getInnerLoc());
  if (Inner.isNull())
    return QualType();
  
  QualType NewTy = Cxt.SemaRef.BuildParenType(Inner);
  if (NewTy.isNull())
    return QualType();
  
  ParenTypeLoc NewTL = TLB.push<ParenTypeLoc>(NewTy);
  NewTL.setLParenLoc(TL.getLParenLoc());
  NewTL.setRParenLoc(TL.getRParenLoc());
  
  return NewTy;
}

static QualType InjectPointerType(InjectionContext &Cxt, 
                                  TypeLocBuilder &TLB, 
                                  PointerTypeLoc TL) {
  QualType Pointee = InjectType(Cxt, TLB, TL.getPointeeLoc());
  if (Pointee.isNull())
    return QualType();
  
  SourceLocation Loc;
  DeclarationName Name;
  QualType NewTy = Cxt.SemaRef.BuildPointerType(Pointee, Loc, Name);
  if (NewTy.isNull())
    return QualType();

  PointerTypeLoc NewTL = TLB.push<PointerTypeLoc>(NewTy);
  NewTL.setSigilLoc(TL.getSigilLoc());
  
  return NewTy;
}

static QualType InjectDecayedType(InjectionContext &Cxt, 
                                  TypeLocBuilder &TLB,
                                  DecayedTypeLoc TL) {
  QualType Orig = InjectType(Cxt, TLB, TL.getOriginalLoc());
  if (Orig.isNull())
    return QualType();
  
  QualType NewTy = getASTContext(Cxt).getDecayedType(Orig);  

  TLB.push<DecayedTypeLoc>(NewTy);

  return NewTy;
}

static QualType InjectLValueReferenceType(InjectionContext &Cxt, 
                                          TypeLocBuilder &TLB,
                                          LValueReferenceTypeLoc TL) {
  QualType Pointee = InjectType(Cxt, TLB, TL.getPointeeLoc());
  if (Pointee.isNull())
    return QualType();
  
  DeclarationName Name;
  QualType NewTy = Cxt.SemaRef.BuildReferenceType(
      Pointee, true, TL.getSigilLoc(), Name);

  LValueReferenceTypeLoc NewTL = TLB.push<LValueReferenceTypeLoc>(NewTy);
  NewTL.setSigilLoc(TL.getSigilLoc());

  return NewTy;
}

static QualType InjectRValueReferenceType(InjectionContext &Cxt,
                                          TypeLocBuilder &TLB,
                                          RValueReferenceTypeLoc TL) {
  QualType Pointee = InjectType(Cxt, TLB, TL.getPointeeLoc());
  if (Pointee.isNull())
    return QualType();
  
  DeclarationName Name;
  QualType NewTy = Cxt.SemaRef.BuildReferenceType(
      Pointee, false, TL.getSigilLoc(), Name);

  RValueReferenceTypeLoc NewTL = TLB.push<RValueReferenceTypeLoc>(NewTy);
  NewTL.setSigilLoc(TL.getSigilLoc());

  return NewTy;
}

static QualType InjectMemberPointerType(InjectionContext &Cxt,
                                        TypeLocBuilder &TLB,
                                        MemberPointerTypeLoc TL) {
  const MemberPointerType *T = TL.getTypePtr();

  QualType Pointee = InjectType(Cxt, TLB, TL.getPointeeLoc());
  if (Pointee.isNull())
    return QualType();

  TypeSourceInfo *NewClassInfo = nullptr;
  if (TypeSourceInfo* OldClassInfo = TL.getClassTInfo()) {
    NewClassInfo = InjectType(Cxt, OldClassInfo);
    if (!NewClassInfo)
      return QualType();
  }

  QualType NewClassTy;
  if (NewClassInfo)
    NewClassTy = NewClassInfo->getType();
  else {
    NewClassTy = InjectType(Cxt, T->getClass());
    if (NewClassTy.isNull())
      return QualType();
  }

  DeclarationName Name;
  QualType Result = Cxt.SemaRef.BuildMemberPointerType(
      Pointee, NewClassTy, TL.getStarLoc(), Name);

  // If we had to adjust the pointee type when building a member pointer, make
  // sure to push TypeLoc info for it.
  const MemberPointerType *MPT = Result->getAs<MemberPointerType>();
  if (MPT && MPT->getPointeeType() != Pointee) {
    assert(isa<AdjustedType>(MPT->getPointeeType()));
    TLB.push<AdjustedTypeLoc>(MPT->getPointeeType());
  }

  MemberPointerTypeLoc NewTL = TLB.push<MemberPointerTypeLoc>(Result);
  NewTL.setSigilLoc(TL.getSigilLoc());
  NewTL.setClassTInfo(NewClassInfo);

  return Result;
}

static QualType InjectArrayType(InjectionContext &Cxt, 
                                TypeLocBuilder &TLB,
                                ConstantArrayTypeLoc TL) {
  const ConstantArrayType *T = TL.getTypePtr();

  QualType Elem = InjectType(Cxt, TLB, TL.getElementLoc());
  if (Elem.isNull())
    return QualType();

  ASTContext &AST = getASTContext(Cxt);
    IntegerLiteral *Count = IntegerLiteral::Create(
    AST, T->getSize(), AST.getSizeType(), SourceLocation());
  
  DeclarationName Name;
  QualType Result =  Cxt.SemaRef.BuildArrayType(
      Elem, T->getSizeModifier(), Count, T->getIndexTypeCVRQualifiers(), 
      TL.getBracketsRange(), Name);
  if (Result.isNull())
    return QualType();

  // We might have either a ConstantArrayType or a VariableArrayType now:
  // a ConstantArrayType is allowed to have an element type which is a
  // VariableArrayType if the type is dependent.  Fortunately, all array
  // types have the same location layout.
  ArrayTypeLoc NewTL = TLB.push<ArrayTypeLoc>(Result);
  NewTL.setLBracketLoc(TL.getLBracketLoc());
  NewTL.setRBracketLoc(TL.getRBracketLoc());

  // Re-evaluate the extent, so that we can add to the type loc.
  Expr *Size = TL.getSizeExpr();
  if (Size) {
    EnterExpressionEvaluationContext Unevaluated(
        Cxt.SemaRef, Sema::ExpressionEvaluationContext::ConstantEvaluated);
    Size = InjectExpr(Cxt, Size).get();
    Size = Cxt.SemaRef.ActOnConstantExpression(Size).get();
  }
  NewTL.setSizeExpr(Size);

  return Result;
}

static QualType InjectArrayType(InjectionContext &Cxt, 
                                TypeLocBuilder &TLB,
                                VariableArrayTypeLoc TL) {
  // FIXME: See TreeTransform.
  llvm_unreachable("not implemented");
}

static QualType InjectArrayType(InjectionContext &Cxt, 
                                TypeLocBuilder &TLB, 
                                IncompleteArrayTypeLoc TL) {
  const IncompleteArrayType *T = TL.getTypePtr();
  QualType Elem = InjectType(Cxt, TLB, TL.getElementLoc());
  if (Elem.isNull())
    return QualType();

  DeclarationName Name;
  QualType Result = Cxt.SemaRef.BuildArrayType(
      Elem, T->getSizeModifier(), nullptr, T->getIndexTypeCVRQualifiers(),
      TL.getBracketsRange(), Name);
  if (Result.isNull())
      return QualType();

  IncompleteArrayTypeLoc NewTL = TLB.push<IncompleteArrayTypeLoc>(Result);
  NewTL.setLBracketLoc(TL.getLBracketLoc());
  NewTL.setRBracketLoc(TL.getRBracketLoc());
  NewTL.setSizeExpr(nullptr);

  return Result;
}

static QualType InjectArrayType(InjectionContext &Cxt, 
                                TypeLocBuilder &TLB,
                                DependentSizedArrayTypeLoc TL) {
  const DependentSizedArrayType *T = TL.getTypePtr();
  QualType Elem = InjectType(Cxt, TLB, TL.getElementLoc());
  if (Elem.isNull())
    return QualType();

  // Array bounds are constant expressions.
  EnterExpressionEvaluationContext Unevaluated(
      Cxt.SemaRef, Sema::ExpressionEvaluationContext::ConstantEvaluated);

  // Prefer the expression from the TypeLoc; the other may have been uniqued.
  Expr *OldSize = TL.getSizeExpr();
  if (!OldSize) 
    OldSize = T->getSizeExpr();

  ExprResult NewSize = InjectExpr(Cxt, OldSize);
  NewSize = Cxt.SemaRef.ActOnConstantExpression(NewSize);
  if (NewSize.isInvalid())
    return QualType();

  DeclarationName Name;
  QualType Result = Cxt.SemaRef.BuildArrayType(
      Elem, T->getSizeModifier(), NewSize.get(), T->getIndexTypeCVRQualifiers(),
      TL.getBracketsRange(), Name);
  if (Result.isNull())
    return QualType();
  
  // We might have any sort of array type now, but fortunately they
  // all have the same location layout.
  ArrayTypeLoc NewTL = TLB.push<ArrayTypeLoc>(Result);
  NewTL.setLBracketLoc(TL.getLBracketLoc());
  NewTL.setRBracketLoc(TL.getRBracketLoc());
  NewTL.setSizeExpr(NewSize.get());

  return Result;
}

static QualType InjectFunctionType(InjectionContext &Cxt,
                                   TypeLocBuilder &TLB,
                                   FunctionProtoTypeLoc TL) {
  const FunctionProtoType *T = TL.getTypePtr();

  // Handle parameters first.
  //
  // FIXME: Handle ExtParameterInfo.
  const QualType * OldParmTypes = TL.getTypePtr()->param_type_begin();
  ArrayRef<ParmVarDecl *> OldParmVars = TL.getParams();
  SmallVector<QualType, 4> NewParmTypes;
  SmallVector<ParmVarDecl *, 4> NewParmVars;
  for (unsigned i = 0; i != OldParmVars.size(); ++i) {
    if (ParmVarDecl *OldParm = OldParmVars[i]) {
      ParmVarDecl *NewParm = cast_or_null<ParmVarDecl>(InjectDecl(Cxt, OldParm));
      if (!NewParm)
        return QualType();
      NewParmTypes.push_back(NewParm->getType());
      NewParmVars.push_back(NewParm);
    } else {
      QualType NewType = InjectType(Cxt, OldParmTypes[i]);
      NewParmTypes.push_back(NewType);
    }
  }

  // Handle the return type. The cases are a bit different for leading vs.
  // trailing return types.
  QualType Ret;
  if (T->hasTrailingReturn()) {
    // FIXME: Not sure about context and quals.
    Sema::CXXThisScopeRAII ThisScope(Cxt.SemaRef, nullptr, 0);
    Ret = InjectType(Cxt, TLB, TL.getReturnLoc());
  } else {
    Ret = InjectType(Cxt, TLB, TL.getReturnLoc());
  }
  if (Ret.isNull())
    return QualType();
  

  // FIXME: Actually transform through the prototype. We may have need
  // to substitute through e.g., noexcept specifiers.
  FunctionProtoType::ExtProtoInfo OldProto = T->getExtProtoInfo();

  SourceLocation Loc;
  DeclarationName Name;
  QualType Result = Cxt.SemaRef.BuildFunctionType(
    Ret, NewParmTypes, Loc, Name, OldProto);

  FunctionProtoTypeLoc NewTL = TLB.push<FunctionProtoTypeLoc>(Result);
  NewTL.setLocalRangeBegin(TL.getLocalRangeBegin());
  NewTL.setLParenLoc(TL.getLParenLoc());
  NewTL.setRParenLoc(TL.getRParenLoc());
  NewTL.setExceptionSpecRange(TL.getExceptionSpecRange());
  NewTL.setLocalRangeEnd(TL.getLocalRangeEnd());
  for (unsigned i = 0, e = NewTL.getNumParams(); i != e; ++i)
    NewTL.setParam(i, NewParmVars[i]);

  return Result;
}

static QualType InjectUnresolvedUsingType(InjectionContext &Cxt,
                                          TypeLocBuilder &TLB,
                                          UnresolvedUsingTypeLoc TL) {
  // Decl *D = ResolveDecl(Cxt, T->getDecl());
  // assert(D); // FIXME: May entail lookup.
  // if (TypeDecl *TD = dyn_cast<TypeDecl>(D))
  //   return getASTContext(Cxt).getTypeDeclType(TD);
  llvm_unreachable("unknown using type");
}

static QualType InjectTypedefType(InjectionContext &Cxt, 
                                  TypeLocBuilder &TLB,
                                  TypedefTypeLoc TL) {
  const TypedefType *T = TL.getTypePtr();
  
  TypedefNameDecl *Typedef = 
      cast_or_null<TypedefNameDecl>(ResolveDecl(Cxt, T->getDecl()));
  if (!Typedef)
    return QualType();

  QualType Result = getASTContext(Cxt).getTypeDeclType(Typedef);
  if (Result.isNull())
    return QualType();

  TypedefTypeLoc NewTL = TLB.push<TypedefTypeLoc>(Result);
  NewTL.setNameLoc(TL.getNameLoc());

  return Result;
}

static QualType InjectRecordType(InjectionContext &Cxt, 
                                 TypeLocBuilder &TLB, 
                                 RecordTypeLoc TL) {
  const RecordType *T = TL.getTypePtr();
  
  RecordDecl *Record = cast_or_null<RecordDecl>(ResolveDecl(Cxt, T->getDecl()));
  if (!Record) 
    return QualType();

  QualType Result = getASTContext(Cxt).getTypeDeclType(Record);
  if (Result.isNull())
    return QualType();

  RecordTypeLoc NewTL = TLB.push<RecordTypeLoc>(Result);
  NewTL.setNameLoc(TL.getNameLoc());

  return Result;
}

static QualType InjectEnumType(InjectionContext &Cxt, 
                               TypeLocBuilder &TLB, 
                               EnumTypeLoc TL) {
  const EnumType *T = TL.getTypePtr();
  
  EnumDecl *Enum = cast_or_null<EnumDecl>(ResolveDecl(Cxt, T->getDecl()));
  if (!Enum)
    return QualType();

  QualType Result = getASTContext(Cxt).getTypeDeclType(Enum);
  if (Result.isNull())
    return QualType();

  EnumTypeLoc NewTL = TLB.push<EnumTypeLoc>(Result);
  NewTL.setNameLoc(TL.getNameLoc());

  return Result;
}

static QualType InjectAutoType(InjectionContext &Cxt,
                               TypeLocBuilder &TLB,
                               AutoTypeLoc TL) {
  const AutoType *T = TL.getTypePtr();
  QualType OldDeduced = T->getDeducedType();
  QualType NewDeduced;
  if (!OldDeduced.isNull()) {
    NewDeduced = InjectType(Cxt, OldDeduced);
    if (NewDeduced.isNull())
      return QualType();
  }

  QualType Result = getASTContext(Cxt).getAutoType(
      NewDeduced, T->getKeyword(), /*IsDependent=*/false);
  if (Result.isNull())
    return QualType();

  AutoTypeLoc NewTL = TLB.push<AutoTypeLoc>(Result);
  NewTL.setNameLoc(TL.getNameLoc());

  return Result;
}

QualType BuildQualifiedType(InjectionContext &Cxt, 
                            QualType T, 
                            SourceLocation Loc, 
                            Qualifiers Quals) {
  // C++ [dcl.fct]p7:
  //   [When] adding cv-qualifications on top of the function type [...] the
  //   cv-qualifiers are ignored.
  // C++ [dcl.ref]p1:
  //   when the cv-qualifiers are introduced through the use of a typedef-name
  //   or decltype-specifier [...] the cv-qualifiers are ignored.
  // Note that [dcl.ref]p1 lists all cases in which cv-qualifiers can be
  // applied to a reference type.
  // FIXME: This removes all qualifiers, not just cv-qualifiers!
  if (T->isFunctionType() || T->isReferenceType())
    return T;

  // Suppress Objective-C lifetime qualifiers if they don't make sense for the
  // resulting type.
  if (Quals.hasObjCLifetime()) {
    if (!T->isObjCLifetimeType() && !T->isDependentType())
      Quals.removeObjCLifetime();
    else if (T.getObjCLifetime()) {
      // Objective-C ARC:
      //   A lifetime qualifier applied to a substituted template parameter
      //   overrides the lifetime qualifier from the template argument.
      const AutoType *AutoTy;
      if (const SubstTemplateTypeParmType *SubstTypeParam
                                = dyn_cast<SubstTemplateTypeParmType>(T)) {
        QualType Replacement = SubstTypeParam->getReplacementType();
        Qualifiers Qs = Replacement.getQualifiers();
        Qs.removeObjCLifetime();
        Replacement = getASTContext(Cxt).getQualifiedType(
            Replacement.getUnqualifiedType(), Qs);
        T = getASTContext(Cxt).getSubstTemplateTypeParmType(
            SubstTypeParam->getReplacedParameter(), Replacement);
      } else if ((AutoTy = dyn_cast<AutoType>(T)) && AutoTy->isDeduced()) {
        // 'auto' types behave the same way as template parameters.
        QualType Deduced = AutoTy->getDeducedType();
        Qualifiers Qs = Deduced.getQualifiers();
        Qs.removeObjCLifetime();
        Deduced = getASTContext(Cxt).getQualifiedType(
              Deduced.getUnqualifiedType(), Qs);
        T = getASTContext(Cxt).getAutoType(
              Deduced, AutoTy->getKeyword(), AutoTy->isDependentType());
      } else {
        // Otherwise, complain about the addition of a qualifier to an
        // already-qualified type.
        // FIXME: Why is this check not in Sema::BuildQualifiedType?
        Cxt.SemaRef.Diag(Loc, diag::err_attr_objc_ownership_redundant) << T;
        Quals.removeObjCLifetime();
      }
    }
  }

  return Cxt.SemaRef.BuildQualifiedType(T, Loc, Quals);
}

static QualType InjectQualifiedType(InjectionContext &Cxt,
                                    TypeLocBuilder &TLB,
                                    QualifiedTypeLoc TL) {
  Qualifiers Quals = TL.getType().getLocalQualifiers();
  QualType Result = InjectType(Cxt, TLB, TL.getUnqualifiedLoc());
  if (Result.isNull())
    return QualType();

  Result = BuildQualifiedType(Cxt, Result, TL.getBeginLoc(), Quals);

  // RebuildQualifiedType might have updated the type, but not in a way
  // that invalidates the TypeLoc. (There's no location information for
  // qualifiers.)
  TLB.TypeWasModifiedSafely(Result);

  return Result;
}

static QualType InjectTemplateTypeParmType(InjectionContext &Cxt,
                                           TypeLocBuilder &TLB,
                                           TemplateTypeParmTypeLoc TL) {
  return InjectTypeSpecType(Cxt, TLB, TL);
}

static QualType InjectTemplateTypeParmType(InjectionContext &Cxt, 
                                           TypeLocBuilder &TLB, 
                                           SubstTemplateTypeParmTypeLoc TL) {
  const SubstTemplateTypeParmType *T = TL.getTypePtr();

  QualType Replacement = InjectType(Cxt, T->getReplacementType());
  if (Replacement.isNull())
    return QualType();

  Replacement = getASTContext(Cxt).getCanonicalType(Replacement);
  QualType Result = getASTContext(Cxt).getSubstTemplateTypeParmType(
      T->getReplacedParameter(), Replacement);

  SubstTemplateTypeParmTypeLoc NewTL
    = TLB.push<SubstTemplateTypeParmTypeLoc>(Result);
  NewTL.setNameLoc(TL.getNameLoc());
  return Result;
}

// FIXME: Implement me. Also, we're probably going to need to use the
// TLB facility to do this "correctly".
QualType InjectType(InjectionContext &Cxt, TypeLocBuilder &TLB, TypeLoc TL) {
  switch (TL.getTypeLocClass()) {
  case TypeLoc::Builtin:
    return InjectBuiltinType(Cxt, TLB, TL.castAs<BuiltinTypeLoc>());
  case TypeLoc::Complex:
    return InjectComplexType(Cxt, TLB, TL.castAs<ComplexTypeLoc>());
  case TypeLoc::Paren:
    return InjectParenType(Cxt, TLB, TL.castAs<ParenTypeLoc>());
  case TypeLoc::Pointer:
    return InjectPointerType(Cxt, TLB, TL.castAs<PointerTypeLoc>());
  case TypeLoc::Decayed:
    return InjectDecayedType(Cxt, TLB, TL.castAs<DecayedTypeLoc>());
  case TypeLoc::LValueReference:
    return InjectLValueReferenceType(Cxt, TLB, TL.castAs<LValueReferenceTypeLoc>());
  case TypeLoc::RValueReference:
    return InjectRValueReferenceType(Cxt, TLB, TL.castAs<RValueReferenceTypeLoc>());
  case TypeLoc::MemberPointer:
    return InjectMemberPointerType(Cxt, TLB, TL.castAs<MemberPointerTypeLoc>());
  case TypeLoc::ConstantArray:
    return InjectArrayType(Cxt, TLB, TL.castAs<ConstantArrayTypeLoc>());
  case TypeLoc::VariableArray:
    return InjectArrayType(Cxt, TLB, TL.castAs<VariableArrayTypeLoc>());
  case TypeLoc::IncompleteArray:
    return InjectArrayType(Cxt, TLB, TL.castAs<IncompleteArrayTypeLoc>());
  case TypeLoc::DependentSizedArray:
    return InjectArrayType(Cxt, TLB, TL.castAs<DependentSizedArrayTypeLoc>());
  case TypeLoc::FunctionProto:
    return InjectFunctionType(Cxt, TLB, TL.castAs<FunctionProtoTypeLoc>());
  case TypeLoc::UnresolvedUsing:
    return InjectUnresolvedUsingType(Cxt, TLB, TL.castAs<UnresolvedUsingTypeLoc>());
  case TypeLoc::Typedef:
    return InjectTypedefType(Cxt, TLB, TL.castAs<TypedefTypeLoc>());
  case TypeLoc::Record:
    return InjectRecordType(Cxt, TLB, TL.castAs<RecordTypeLoc>());
  case TypeLoc::Enum:
    return InjectEnumType(Cxt, TLB, TL.castAs<EnumTypeLoc>());
  case TypeLoc::Auto:
    return InjectAutoType(Cxt, TLB, TL.castAs<AutoTypeLoc>());
  case TypeLoc::Qualified:
    return InjectQualifiedType(Cxt, TLB, TL.castAs<QualifiedTypeLoc>());
  case TypeLoc::TemplateTypeParm:
    return InjectTemplateTypeParmType(Cxt, TLB, TL.castAs<TemplateTypeParmTypeLoc>());
  case TypeLoc::SubstTemplateTypeParm:
    return InjectTemplateTypeParmType(Cxt, TLB, TL.castAs<SubstTemplateTypeParmTypeLoc>());
  default:
    TL.getType()->dump();
    llvm_unreachable("Unknown type");
  }
}

QualType InjectType(InjectionContext &Cxt, QualType T) {
  TypeSourceInfo *Old = getASTContext(Cxt).getTrivialTypeSourceInfo(T);
  TypeSourceInfo *New = InjectType(Cxt, Old);
  if (!New)
    return QualType();
  return New->getType();
}


QualType InjectType(InjectionContext &Cxt, const Type *T) {
  return InjectType(Cxt, QualType(T, 0));
}

TypeSourceInfo *InjectType(InjectionContext &Cxt, TypeSourceInfo *TSI) {
  if (!TSI)
    return nullptr;
  TypeLocBuilder TLB;
  TypeLoc TL = TSI->getTypeLoc();
  TLB.reserve(TL.getFullDataSize());
  QualType T = InjectType(Cxt, TLB, TL);
  if (T.isNull())
    return nullptr;
  return TLB.getTypeSourceInfo(getASTContext(Cxt), T);
}

TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, ValueDecl *D) {
  QualType T = InjectType(Cxt, D->getType());
  return getASTContext(Cxt).getTrivialTypeSourceInfo(T);
}

TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, DeclaratorDecl *D) {
  return InjectType(Cxt, D->getTypeSourceInfo());
}

QualType InjectDeducibleType(InjectionContext &Cxt, QualType T) {
  if (!isa<DependentNameType>(T))
    return InjectType(Cxt, T);

  TypeSourceInfo *OldTSI = getASTContext(Cxt).getTrivialTypeSourceInfo(T);
  TypeSourceInfo *NewTSI = InjectDeducibleType(Cxt, OldTSI);
  if (!NewTSI)
    return QualType();
  return NewTSI->getType();
}

static QualType RebuildDependentNameType(InjectionContext& Cxt, 
                                         ElaboratedTypeKeyword Keyword, 
                                         SourceLocation KeywordLoc, 
                                         NestedNameSpecifierLoc QualifierLoc, 
                                         const IdentifierInfo *Id, 
                                         SourceLocation IdLoc, 
                                         bool DeducedTSTContext) {
  CXXScopeSpec SS;
  SS.Adopt(QualifierLoc);

  if (QualifierLoc.getNestedNameSpecifier()->isDependent()) {
    // If the name is still dependent, just build a new dependent name type.
    if (!Cxt.SemaRef.computeDeclContext(SS))
      return getASTContext(Cxt).getDependentNameType(
          Keyword, QualifierLoc.getNestedNameSpecifier(), Id);
  }

  if (Keyword == ETK_None || Keyword == ETK_Typename) {
    QualType T = Cxt.SemaRef.CheckTypenameType(
        Keyword, KeywordLoc, QualifierLoc, *Id, IdLoc);
    
    // If a dependent name resolves to a deduced template specialization type,
    // check that we're in one of the syntactic contexts permitting it.
    if (!DeducedTSTContext) {
      if (auto *Deduced = dyn_cast_or_null<DeducedTemplateSpecializationType>(
              T.isNull() ? nullptr : T->getContainedDeducedType())) {
        Cxt.SemaRef.Diag(IdLoc, diag::err_dependent_deduced_tst)
          << (int)Cxt.SemaRef.getTemplateNameKindForDiagnostics(
                 Deduced->getTemplateName())
          << QualType(QualifierLoc.getNestedNameSpecifier()->getAsType(), 0);
        if (auto *TD = Deduced->getTemplateName().getAsTemplateDecl())
          Cxt.SemaRef.Diag(TD->getLocation(), diag::note_template_decl_here);
        return QualType();
      }
    }
    return T;
  }

  TagTypeKind Kind = TypeWithKeyword::getTagTypeKindForKeyword(Keyword);

  // We had a dependent elaborated-type-specifier that has been transformed
  // into a non-dependent elaborated-type-specifier. Find the tag we're
  // referring to.
  LookupResult Result(Cxt.SemaRef, Id, IdLoc, Sema::LookupTagName);
  DeclContext *DC = Cxt.SemaRef.computeDeclContext(SS, false);
  if (!DC)
    return QualType();

  if (Cxt.SemaRef.RequireCompleteDeclContext(SS, DC))
    return QualType();

  TagDecl *Tag = nullptr;
  Cxt.SemaRef.LookupQualifiedName(Result, DC);
  switch (Result.getResultKind()) {
    case LookupResult::NotFound:
    case LookupResult::NotFoundInCurrentInstantiation:
      break;

    case LookupResult::Found:
      Tag = Result.getAsSingle<TagDecl>();
      break;

    case LookupResult::FoundOverloaded:
    case LookupResult::FoundUnresolvedValue:
      llvm_unreachable("Tag lookup cannot find non-tags");

    case LookupResult::Ambiguous:
      // Let the LookupResult structure handle ambiguities.
      return QualType();
  }

  if (!Tag) {
    // Check where the name exists but isn't a tag type and use that to emit
    // better diagnostics.
    LookupResult Result(Cxt.SemaRef, Id, IdLoc, Sema::LookupTagName);
    Cxt.SemaRef.LookupQualifiedName(Result, DC);
    switch (Result.getResultKind()) {
      case LookupResult::Found:
      case LookupResult::FoundOverloaded:
      case LookupResult::FoundUnresolvedValue: {
        NamedDecl *SomeDecl = Result.getRepresentativeDecl();
        Sema::NonTagKind NTK = Cxt.SemaRef.getNonTagTypeDeclKind(SomeDecl, Kind);
        Cxt.SemaRef.Diag(IdLoc, diag::err_tag_reference_non_tag) << SomeDecl
                                                                 << NTK 
                                                                 << Kind;
        Cxt.SemaRef.Diag(SomeDecl->getLocation(), diag::note_declared_at);
        break;
      }
      default:
        Cxt.SemaRef.Diag(IdLoc, diag::err_not_tag_in_scope)
            << Kind << Id << DC << QualifierLoc.getSourceRange();
        break;
    }
    return QualType();
  }

  if (!Cxt.SemaRef.isAcceptableTagRedeclaration(
      Tag, Kind, /*isDefinition*/false, IdLoc, Id)) {
    Cxt.SemaRef.Diag(KeywordLoc, diag::err_use_with_wrong_tag) << Id;
    Cxt.SemaRef.Diag(Tag->getLocation(), diag::note_previous_use);
    return QualType();
  }

  // Build the elaborated-type-specifier type.
  QualType T = getASTContext(Cxt).getTypeDeclType(Tag);
  return getASTContext(Cxt).getElaboratedType(
      Keyword, QualifierLoc.getNestedNameSpecifier(), T);
}


static QualType InjectDepedentTypeName(InjectionContext &Cxt,
                                       TypeLocBuilder &TLB,
                                       DependentNameTypeLoc TL,
                                       bool DeducedContext = false) {
  const DependentNameType *T = TL.getTypePtr();

  NestedNameSpecifierLoc OldNNS = TL.getQualifierLoc();
  NestedNameSpecifierLoc NewNNS = InjectNameSpecifier(Cxt, OldNNS);
  if (!NewNNS)
    return QualType();

  QualType Result = RebuildDependentNameType(
      Cxt, T->getKeyword(), TL.getElaboratedKeywordLoc(), NewNNS,
      T->getIdentifier(), TL.getNameLoc(), DeducedContext);
  
  if (Result.isNull())
    return QualType();

  if (const ElaboratedType* ElabT = Result->getAs<ElaboratedType>()) {
    QualType NamedT = ElabT->getNamedType();
    TLB.pushTypeSpec(NamedT).setNameLoc(TL.getNameLoc());
    ElaboratedTypeLoc NewTL = TLB.push<ElaboratedTypeLoc>(Result);
    NewTL.setElaboratedKeywordLoc(TL.getElaboratedKeywordLoc());
    NewTL.setQualifierLoc(NewNNS);
  } else {
    DependentNameTypeLoc NewTL = TLB.push<DependentNameTypeLoc>(Result);
    NewTL.setElaboratedKeywordLoc(TL.getElaboratedKeywordLoc());
    NewTL.setQualifierLoc(NewNNS);
    NewTL.setNameLoc(TL.getNameLoc());
  }
  return Result;
}

static QualType RebuildQualifiedType(InjectionContext &Cxt,
                                     QualType T, 
                                     SourceLocation Loc, 
                                     Qualifiers Quals) {
  // C++ [dcl.fct]p7:
  //   [When] adding cv-qualifications on top of the function type [...] the
  //   cv-qualifiers are ignored.
  // C++ [dcl.ref]p1:
  //   when the cv-qualifiers are introduced through the use of a typedef-name
  //   or decltype-specifier [...] the cv-qualifiers are ignored.
  // Note that [dcl.ref]p1 lists all cases in which cv-qualifiers can be
  // applied to a reference type.
  // FIXME: This removes all qualifiers, not just cv-qualifiers!
  if (T->isFunctionType() || T->isReferenceType())
    return T;

  // Suppress Objective-C lifetime qualifiers if they don't make sense for the
  // resulting type.
  if (Quals.hasObjCLifetime()) {
    if (!T->isObjCLifetimeType() && !T->isDependentType())
      Quals.removeObjCLifetime();
    else if (T.getObjCLifetime()) {
      // Objective-C ARC:
      //   A lifetime qualifier applied to a substituted template parameter
      //   overrides the lifetime qualifier from the template argument.
      const AutoType *AutoTy;
      if (const SubstTemplateTypeParmType *SubstTypeParam
                                = dyn_cast<SubstTemplateTypeParmType>(T)) {
        QualType Replacement = SubstTypeParam->getReplacementType();
        Qualifiers Qs = Replacement.getQualifiers();
        Qs.removeObjCLifetime();
        Replacement = getASTContext(Cxt).getQualifiedType(
            Replacement.getUnqualifiedType(), Qs);
        T = getASTContext(Cxt).getSubstTemplateTypeParmType(
            SubstTypeParam->getReplacedParameter(), Replacement);
      } else if ((AutoTy = dyn_cast<AutoType>(T)) && AutoTy->isDeduced()) {
        // 'auto' types behave the same way as template parameters.
        QualType Deduced = AutoTy->getDeducedType();
        Qualifiers Qs = Deduced.getQualifiers();
        Qs.removeObjCLifetime();
        Deduced =
            getASTContext(Cxt).getQualifiedType(Deduced.getUnqualifiedType(), Qs);
        T = getASTContext(Cxt).getAutoType(Deduced, AutoTy->getKeyword(),
                                          AutoTy->isDependentType());
      } else {
        // Otherwise, complain about the addition of a qualifier to an
        // already-qualified type.
        // FIXME: Why is this check not in Sema::BuildQualifiedType?
        Cxt.SemaRef.Diag(Loc, diag::err_attr_objc_ownership_redundant) << T;
        Quals.removeObjCLifetime();
      }
    }
  }

  return Cxt.SemaRef.BuildQualifiedType(T, Loc, Quals);
}

TypeSourceInfo *InjectDeducibleType(InjectionContext &Cxt, TypeSourceInfo *TSI) {
  if (!isa<DependentNameType>(TSI->getType()))
    return InjectType(Cxt, TSI);


  TypeLocBuilder TLB;
  TypeLoc TL = TSI->getTypeLoc();
  TLB.reserve(TL.getFullDataSize());

  Qualifiers Quals;
  auto QTL = TL.getAs<QualifiedTypeLoc>();
  if (QTL)
    TL = QTL.getUnqualifiedLoc();

  auto DNTL = TL.castAs<DependentNameTypeLoc>();

  QualType Result = InjectDepedentTypeName(Cxt, TLB, DNTL, /*DeducedContext=*/true);
  if (Result.isNull())
    return nullptr;

  if (QTL) {
    Result = RebuildQualifiedType(
        Cxt, Result, QTL.getBeginLoc(), QTL.getType().getLocalQualifiers());
    TLB.TypeWasModifiedSafely(Result);
  }

  return TLB.getTypeSourceInfo(getASTContext(Cxt), Result);
}


// Statements

StmtResult InjectCompoundStmt(InjectionContext &Cxt, CompoundStmt *S) {
  Sema::CompoundScopeRAII CompoundScope(Cxt.SemaRef);
  SmallVector<Stmt*, 8> Statements;
  for (auto *B : S->body()) {
    StmtResult Result = InjectStmt(Cxt, B);
    if (Result.isInvalid())
      return StmtError();
    Statements.push_back(Result.get());
  }
  return Cxt.SemaRef.ActOnCompoundStmt(S->getLocStart(), 
                                       S->getLocEnd(), 
                                       Statements, 
                                       false);
}

static Sema::ConditionResult InjectCondition(InjectionContext &Cxt,
                                             SourceLocation Loc,
                                             VarDecl *Var,
                                             Expr *Cond,
                                             Sema::ConditionKind Kind) {
  if (Var) {
    VarDecl *CondVar = cast_or_null<VarDecl>(InjectDecl(Cxt, Var));
    if (!CondVar)
      return Sema::ConditionError();
    return Cxt.SemaRef.ActOnConditionVariable(CondVar, Loc, Kind);
  }

  if (Cond) {
    ExprResult CondExpr = InjectExpr(Cxt, Cond);
    if (CondExpr.isInvalid())
      return Sema::ConditionError();
    return Cxt.SemaRef.ActOnCondition(nullptr, Loc, CondExpr.get(), Kind);
  }

  return Sema::ConditionResult();
}

StmtResult InjectIfStmt(InjectionContext &Cxt, IfStmt *S) {
  // Transform the initialization statement
  StmtResult Init = InjectStmt(Cxt, S->getInit());
  if (Init.isInvalid())
    return StmtError();

  // Transform the condition
  Sema::ConditionKind Kind = S->isConstexpr() ? 
      Sema::ConditionKind::ConstexprIf :
      Sema::ConditionKind::Boolean;
  Sema::ConditionResult Cond = InjectCondition(Cxt, S->getIfLoc(),
                                               S->getConditionVariable(),
                                               S->getCond(),
                                               Kind);
  if (Cond.isInvalid())
    return StmtError();

  // If this is a constexpr if, determine which arm we should instantiate.
  llvm::Optional<bool> ConstexprConditionValue;
  if (S->isConstexpr())
    ConstexprConditionValue = Cond.getKnownValue();

  // Transform the "then" branch.
  StmtResult Then;
  if (!ConstexprConditionValue || *ConstexprConditionValue) {
    Then = InjectStmt(Cxt, S->getThen());
    if (Then.isInvalid())
      return StmtError();
  } else {
    Then = new (Cxt.SemaRef.Context) NullStmt(S->getThen()->getLocStart());
  }

  // Transform the "else" branch.
  StmtResult Else;
  if (!ConstexprConditionValue || !*ConstexprConditionValue) {
    Else = InjectStmt(Cxt, S->getElse());
    if (Else.isInvalid())
      return StmtError();
  }

  return Cxt.SemaRef.ActOnIfStmt(S->getIfLoc(), S->isConstexpr(), Init.get(), 
                                 Cond, Then.get(), S->getElseLoc(), Else.get());

}

StmtResult InjectWhileStmt(InjectionContext &Cxt, WhileStmt *S) {
  llvm_unreachable("not implemented");
}

StmtResult InjectDoStmt(InjectionContext &Cxt, DoStmt *S) {
  llvm_unreachable("not implemented");
}

StmtResult InjectReturnStmt(InjectionContext &Cxt, ReturnStmt *S) {
  // FIXME: This is wrong. We need an InjectInitializer to handle case
  // where initializers are allowed.
  ExprResult Return = InjectExpr(Cxt, S->getRetValue());
  if (Return.isInvalid())
    return StmtError();
  return Cxt.SemaRef.BuildReturnStmt(S->getLocStart(), Return.get());
}

StmtResult InjectExprStmt(InjectionContext &Cxt, Expr *E) {
  ExprResult Result = InjectExpr(Cxt, E);
  if (Result.isInvalid())
    return StmtError();
  return StmtResult(Result.get());
}

StmtResult InjectDeclStmt(InjectionContext &Cxt, DeclStmt *S) {
  SmallVector<Decl *, 4> Decls;
  for (auto *OldDecl : S->decls()) {
    Decl *NewDecl = InjectDecl(Cxt, OldDecl);
    if (!NewDecl)
      return StmtError();
    Decls.push_back(NewDecl);
  }

  Sema::DeclGroupPtrTy DG = Cxt.SemaRef.BuildDeclaratorGroup(Decls);
  return Cxt.SemaRef.ActOnDeclStmt(DG, S->getStartLoc(), S->getEndLoc());
}

StmtResult InjectStmt(InjectionContext &Cxt, Stmt *S) {
  if (!S)
    return StmtResult();
  switch (S->getStmtClass()) {
  case Stmt::NullStmtClass:
  case Stmt::BreakStmtClass:
  case Stmt::ContinueStmtClass:
    return S;

  case Stmt::CompoundStmtClass:
    return InjectCompoundStmt(Cxt, cast<CompoundStmt>(S));
  
  // case Stmt::LabelStmtClass:
  // case Stmt::GotoStmtClass:
  // case Stmt::IndirectGotoStmtClass:

  // case Stmt::AttributedStmtClass:
  
  case Stmt::IfStmtClass:
    return InjectIfStmt(Cxt, cast<IfStmt>(S));
  case Stmt::WhileStmtClass:
    return InjectWhileStmt(Cxt, cast<WhileStmt>(S));
  case Stmt::DoStmtClass:
    return InjectDoStmt(Cxt, cast<DoStmt>(S));

  // case Stmt::ForStmtClass:
  
  // case Stmt::SwitchStmtClass:
  // case Stmt::SwitchCaseClass:
  // case Stmt::CaseStmtClass:
  // case Stmt::DefaultStmtClass:

  case Stmt::ReturnStmtClass:
    return InjectReturnStmt(Cxt, cast<ReturnStmt>(S));
  
  case Stmt::DeclStmtClass:
    return InjectDeclStmt(Cxt, cast<DeclStmt>(S));

  // case Stmt::CapturedStmtClass:

  default: {
    if (Expr *E = dyn_cast<Expr>(S))
      return InjectExprStmt(Cxt, E);

    S->dump();
    llvm_unreachable("Unknown statement");
  }
  }
}

StmtResult InjectStmt(InjectionContext &Cxt, StmtResult S) {
  return InjectStmt(Cxt, S.get());
}

// Expressions

// Transforms the explicit template arguments for the given type expression,
// filling Args with template arguments (if any). The Output pointer is 
// assigned to &Args if arguments are present, otherwise nullptr. Returns
// true if no errors are encountered.
template<typename ExprType>
static bool InjectExplicitTemplateArgs(InjectionContext &Cxt, ExprType *E, 
                                       TemplateArgumentListInfo &Args,
                                       TemplateArgumentListInfo *&Output,
                                       SourceLocation &TemplateLoc) {
  if (E->hasExplicitTemplateArgs()) {
    Args.setLAngleLoc(E->getLAngleLoc());
    Args.setRAngleLoc(E->getRAngleLoc());
    const TemplateArgumentLoc *Input = E->getTemplateArgs();
    unsigned Count = E->getNumTemplateArgs();
    if (!InjectTemplateArguments(Cxt, Input, Count, Args))
      return false;
    Output = &Args;
  } else {
    Output = nullptr;
  }
  TemplateLoc = E->getTemplateKeywordLoc();
  return true;
}

ExprResult InjectDeclRefExpr(InjectionContext &Cxt, DeclRefExpr *E) {
  // If the expression is a placeholder, then we should have a replacement
  // available.
  if (Expr *Repl = Cxt.GetPlaceholderReplacement(E))
    return Repl;
 
  // Transform the nested name specifier (if any).
  NestedNameSpecifierLoc QualifierLoc;
  if (E->getQualifier()) {
    QualifierLoc = InjectNameSpecifier(Cxt, E->getQualifierLoc());
    if (!QualifierLoc)
      return ExprError();
  }

  // Transform the member name (if present).
  DeclarationNameInfo NameInfo = E->getNameInfo();
  if (NameInfo.getName()) {
    NameInfo = InjectDeclName(Cxt, NameInfo);
    if (!NameInfo.getName())
      return ExprError();
  }

  // Transform explicit template arguments, if any.
  TemplateArgumentListInfo TemplateArgs;
  TemplateArgumentListInfo *ExplicitArgs;
  SourceLocation TemplateLoc;
  if (!InjectExplicitTemplateArgs(Cxt, E, TemplateArgs, ExplicitArgs, TemplateLoc))
    return ExprError();

  // Try resolving the reference.
  ValueDecl *Value = cast_or_null<ValueDecl>(ResolveDecl(Cxt, E->getDecl()));
  if (!Value) {
    E->dump();
    llvm_unreachable("FAIL");
  }

  CXXScopeSpec SS;
  SS.Adopt(QualifierLoc);

  return Cxt.SemaRef.BuildDeclarationNameExpr(
    SS, NameInfo, Value, /*FoundDecl=*/nullptr, ExplicitArgs);
}


ExprResult InjectDeclRefExpr(InjectionContext &Cxt, DependentScopeDeclRefExpr *E) {
  // Transform the nested name specifier (if any).
  NestedNameSpecifierLoc QualifierLoc;
  if (E->getQualifier()) {
    QualifierLoc = InjectNameSpecifier(Cxt, E->getQualifierLoc());
    if (!QualifierLoc)
      return ExprError();
  }

  // Transform the member name (if present).
  DeclarationNameInfo NameInfo = E->getNameInfo();
  if (NameInfo.getName()) {
    NameInfo = InjectDeclName(Cxt, NameInfo);
    if (!NameInfo.getName())
      return ExprError();
  }

  // Transform explicit template arguments, if any.
  TemplateArgumentListInfo TemplateArgs;
  TemplateArgumentListInfo *ExplicitArgs;
  SourceLocation TemplateLoc;
  if (!InjectExplicitTemplateArgs(Cxt, E, TemplateArgs, ExplicitArgs, TemplateLoc))
    return ExprError();

  CXXScopeSpec SS;
  SS.Adopt(QualifierLoc);

  if (!ExplicitArgs)
    return Cxt.SemaRef.BuildQualifiedDeclarationNameExpr(
        SS, NameInfo, /*IsAddressOf=*/false, /*Scope=*/nullptr);
  else
    return Cxt.SemaRef.BuildQualifiedTemplateIdExpr(
        SS, TemplateLoc, NameInfo, &TemplateArgs);
}

ExprResult InjectParenExpr(InjectionContext &Cxt, ParenExpr *E) {
  ExprResult Inner = InjectExpr(Cxt, E->getSubExpr());
  if (Inner.isInvalid())
    return ExprError();
  return Cxt.SemaRef.ActOnParenExpr(E->getLocStart(), 
                                    E->getLocEnd(), 
                                    Inner.get());
}

bool InjectArgs(InjectionContext &Cxt, 
                Expr *const *Args, 
                unsigned NumArgs, 
                SmallVectorImpl<Expr *> &Out) {
  for (unsigned I = 0; I != NumArgs; ++I) {
    ExprResult Arg = InjectInit(Cxt, Args[I], /*NotCopyInit=*/false);
    if (Arg.isInvalid())
      return false;
    Out.push_back(Arg.get());
  }
  return true;
}

bool InjectExprs(InjectionContext &Cxt, 
                 Expr *const *Args, 
                 unsigned NumArgs, 
                 SmallVectorImpl<Expr *> &Out) {
  for (unsigned I = 0; I != NumArgs; ++I) {
    ExprResult Arg = InjectExpr(Cxt, Args[I]);
    if (Arg.isInvalid())
      return false;
    Out.push_back(Arg.get());
  }
  return true;
}

ExprResult InjectCallExpr(InjectionContext &Cxt, CallExpr *E) {
  // Transform the callee.
  ExprResult Callee = InjectExpr(Cxt, E->getCallee());
  if (Callee.isInvalid())
    return ExprError();

  // Transform arguments.
  SmallVector<Expr*, 8> Args;
  if (!InjectArgs(Cxt, E->getArgs(), E->getNumArgs(), Args))
    return ExprError();

  CallExpr *CalleeExpr = cast<CallExpr>(Callee.get());
  SourceLocation LParenLoc = CalleeExpr->getLocStart();
  SourceLocation RParenLoc = CalleeExpr->getRParenLoc();

  return Cxt.SemaRef.ActOnCallExpr(
      /*Scope=*/nullptr, CalleeExpr, LParenLoc, Args, RParenLoc, 
      /*ExecConfig*/nullptr);
}

ExprResult InjectAddressOfOperand(InjectionContext &Cxt, Expr *E) {
  if (DependentScopeDeclRefExpr *DRE = dyn_cast<DependentScopeDeclRefExpr>(E))
    return InjectDeclRefExpr(Cxt, DRE);
  else
    return InjectExpr(Cxt, E);
}

ExprResult
RebuildCXXOperatorCallExpr(InjectionContext &Cxt,
                           OverloadedOperatorKind Op, 
                           SourceLocation OpLoc, 
                           Expr *OrigCallee, 
                           Expr *First, 
                           Expr *Second) {
  Expr *Callee = OrigCallee->IgnoreParenCasts();
  QualType FirstTy = First->getType();
  QualType SecondTy = Second->getType();
  
  bool IsPost = Second && (Op == OO_PlusPlus || Op == OO_MinusMinus);


  // Determine whether this should be a builtin operation.
  if (Op == OO_Subscript) {
    if (!First->getType()->isOverloadableType() && 
        !Second->getType()->isOverloadableType())
      return Cxt.SemaRef.CreateBuiltinArraySubscriptExpr(
            First, Callee->getLocStart(), Second, OpLoc);
  } else if (Op == OO_Arrow) {
    // -> is never a builtin operation.
    return Cxt.SemaRef.BuildOverloadedArrowExpr(nullptr, First, OpLoc);
  } else if (Second == nullptr || IsPost) {
    if (!FirstTy->isOverloadableType()) {
      // The argument is not of overloadable type, so try to create a
      // built-in unary operation.
      UnaryOperatorKind Opc = UnaryOperator::getOverloadedOpcode(Op, IsPost);
      return Cxt.SemaRef.CreateBuiltinUnaryOp(OpLoc, Opc, First);
    }
  } else {
    if (!FirstTy->isOverloadableType() && !SecondTy->isOverloadableType()) {
      // Neither of the arguments is an overloadable type, so try to
      // create a built-in binary operation.
      BinaryOperatorKind Opc = BinaryOperator::getOverloadedOpcode(Op);
      return Cxt.SemaRef.CreateBuiltinBinOp(OpLoc, Opc, First, Second);
    }
  }

  // Compute the transformed set of functions (and function templates) to be
  // used during overload resolution.
  UnresolvedSet<16> Functions;

  if (UnresolvedLookupExpr *ULE = dyn_cast<UnresolvedLookupExpr>(Callee)) {
    assert(ULE->requiresADL());
    Functions.append(ULE->decls_begin(), ULE->decls_end());
  } else {
    // If we've resolved this to a particular non-member function, just call
    // that function. If we resolved it to a member function,
    // CreateOverloaded* will find that function for us.
    NamedDecl *ND = cast<DeclRefExpr>(Callee)->getDecl();
    if (!isa<CXXMethodDecl>(ND))
      Functions.addDecl(ND);
  }

  // Add any functions found via argument-dependent lookup.
  Expr *Args[2] = { First, Second };
  unsigned NumArgs = 1 + (Second != nullptr);

  // Create the overloaded operator invocation for unary operators.
  if (NumArgs == 1 || IsPost) {
    UnaryOperatorKind Opc = UnaryOperator::getOverloadedOpcode(Op, IsPost);
    return Cxt.SemaRef.CreateOverloadedUnaryOp(OpLoc, Opc, Functions, First);
  }

  if (Op == OO_Subscript) {
    SourceLocation LBrace;
    SourceLocation RBrace;

    if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Callee)) {
        DeclarationNameLoc NameLoc = DRE->getNameInfo().getInfo();
        LBrace = SourceLocation::getFromRawEncoding(
                    NameLoc.CXXOperatorName.BeginOpNameLoc);
        RBrace = SourceLocation::getFromRawEncoding(
                    NameLoc.CXXOperatorName.EndOpNameLoc);
    } else {
        LBrace = Callee->getLocStart();
        RBrace = OpLoc;
    }

    return Cxt.SemaRef.CreateOverloadedArraySubscriptExpr(
        LBrace, RBrace, First, Second);
  }

  // Create the overloaded operator invocation for binary operators.
  BinaryOperatorKind Opc = BinaryOperator::getOverloadedOpcode(Op);
  return Cxt.SemaRef.CreateOverloadedBinOp(OpLoc, Opc, Functions, Args[0], Args[1]);
}

static ExprResult InjectOperatorCallExpr(InjectionContext &Cxt, 
                                         CXXOperatorCallExpr *E) {
  switch (E->getOperator()) {
  case OO_New:
  case OO_Delete:
  case OO_Array_New:
  case OO_Array_Delete:
    llvm_unreachable("new and delete operators cannot use CXXOperatorCallExpr");

  case OO_Call: {
    // This is a call to an object's operator().
    assert(E->getNumArgs() >= 1 && "Object call is missing arguments");

    // Transform the object itself.
    ExprResult Object = InjectExpr(Cxt, E->getArg(0));
    if (Object.isInvalid())
      return ExprError();

    // FIXME: Poor location information
    SourceLocation LParenLoc = 
        Cxt.SemaRef.getLocForEndOfToken(Object.get()->getLocEnd());
    SourceLocation RParenLoc = E->getLocEnd();

    // Transform the call arguments.
    SmallVector<Expr*, 8> Args;
    if (!InjectArgs(Cxt, E->getArgs() + 1, E->getNumArgs() - 1, Args))
      return ExprError();

    return Cxt.SemaRef.ActOnCallExpr(
        /*Scope=*/nullptr, Object.get(), LParenLoc, Args, RParenLoc,
        /*ExecConfig=*/nullptr);
  }

#define OVERLOADED_OPERATOR(Name,Spelling,Token,Unary,Binary,MemberOnly) \
  case OO_##Name:
#define OVERLOADED_OPERATOR_MULTI(Name,Spelling,Unary,Binary,MemberOnly)
#include "clang/Basic/OperatorKinds.def"

  case OO_Subscript:
    // Handled below.
    break;

  case OO_Conditional:
    llvm_unreachable("conditional operator is not actually overloadable");

  case OO_None:
  case NUM_OVERLOADED_OPERATORS:
    llvm_unreachable("not an overloaded operator?");
  }

  ExprResult Callee = InjectExpr(Cxt, E->getCallee());
  if (Callee.isInvalid())
    return ExprError();

  ExprResult First;
  if (E->getOperator() == OO_Amp) 
    First = InjectAddressOfOperand(Cxt, E->getArg(0));
  else
    First = InjectExpr(Cxt, E->getArg(0));
  if (First.isInvalid())
    return ExprError();

  ExprResult Second;
  if (E->getNumArgs() == 2) {
    Second = InjectExpr(Cxt, E->getArg(1));
    if (Second.isInvalid())
      return ExprError();
  }

  Sema::FPContractStateRAII FPContractState(Cxt.SemaRef);
  Cxt.SemaRef.FPFeatures = E->getFPFeatures();

  SourceLocation OpLoc = E->getOperatorLoc();
  return RebuildCXXOperatorCallExpr(
      Cxt, E->getOperator(), OpLoc, Callee.get(), First.get(), Second.get());
}

static ExprResult InjectMemberExpr(InjectionContext &Cxt, MemberExpr *E) {
  // Transform the base expression.
  ExprResult Base = InjectExpr(Cxt, E->getBase());
  if (Base.isInvalid())
    return ExprError();

  // Transform the NNS in the case we have e.g., x.A::B::C.
  NestedNameSpecifierLoc QualifierLoc;
  if (E->hasQualifier()) {
    QualifierLoc = InjectNameSpecifier(Cxt, E->getQualifierLoc());
    if (!QualifierLoc)
      return ExprError();
  }

  // Transform the member name (if present).
  DeclarationNameInfo NameInfo = E->getMemberNameInfo();
  if (NameInfo.getName()) {
    NameInfo = InjectDeclName(Cxt, NameInfo);
    if (!NameInfo.getName())
      return ExprError();
  }

  // Transform explicit template args in the case we have e.g., x.f<5>;
  TemplateArgumentListInfo TemplateArgs;
  TemplateArgumentListInfo* ExplicitArgs;
  SourceLocation TemplateLoc;
  if (!InjectExplicitTemplateArgs(Cxt, E, TemplateArgs, ExplicitArgs, TemplateLoc))
    return ExprError();

  // Resolve the found declaration (although, we may)
  NamedDecl *Member = cast_or_null<NamedDecl>(ResolveDecl(Cxt, E->getMemberDecl()));
  if (!Member) {
    // FIXME: If we can't re-bind the identifier, then (and only then), we
    // need to re-do the lookup. We'll update FoundDecl with the result,
    // if any.
    llvm_unreachable("no prior declaration");
  }

  CXXScopeSpec SS;
  SS.Adopt(QualifierLoc);

  Expr *BaseExpr = Base.get();
  QualType BaseType = BaseExpr->getType();
  if (E->isArrow() && !BaseType->isPointerType())
    return ExprError();

  // FIXME: this involves duplicating earlier analysis in a lot of
  // cases; we should avoid this when possible.
  LookupResult R(Cxt.SemaRef, NameInfo, Sema::LookupMemberName);
  R.addDecl(Member);
  R.resolveKind();

  return Cxt.SemaRef.BuildMemberReferenceExpr(
      BaseExpr, BaseType, E->getOperatorLoc(), E->isArrow(), SS, TemplateLoc, 
      /*FirstQualifierInScope=*/nullptr, R, ExplicitArgs, /*Scope=*/nullptr);
}

static ExprResult InjectMemberExpr(InjectionContext &Cxt, 
                                   CXXDependentScopeMemberExpr *E) {
  // Transform the base expression.
  ExprResult Base = InjectExpr(Cxt, E->getBase());
  if (Base.isInvalid())
    return ExprError();

  QualType BaseType;
  QualType ObjectType;
  if (!E->isImplicitAccess()) {
    // Start the member reference and compute the object's type, separately
    // from the initial transformation.
    ParsedType ObjectTy;
    bool MayBePseudoDestructor = false;
    Base = Cxt.SemaRef.ActOnStartCXXMemberReference(nullptr, Base.get(),
                                                    E->getOperatorLoc(),
                                                    E->isArrow() ? 
                                                      tok::arrow : tok::period,
                                                    ObjectTy,
                                                    MayBePseudoDestructor);
    if (Base.isInvalid())
      return ExprError();

    ObjectType = ObjectTy.get();
    BaseType = Base.get()->getType();
  } else {
    BaseType = Base.get()->getType();
    ObjectType = BaseType->getAs<PointerType>()->getPointeeType();
  }

  // Transform the member name (if present).
  DeclarationNameInfo NameInfo = InjectDeclName(Cxt, E->getMemberNameInfo());
  if (!NameInfo.getName())
    return ExprError();

  // Transform the NNS in the case we have e.g., x.A::B::C.
  //
  // FIXME: Probably try resolving first qualifier in the NNS. That will
  // probably have the effect of "rebasing" the lookup below.
  NestedNameSpecifierLoc QualifierLoc;
  if (E->getQualifier()) {
    QualifierLoc = InjectNameSpecifier(Cxt, E->getQualifierLoc(), nullptr);
    if (!QualifierLoc)
      return ExprError();
  }

  // Transform explicit template args in the case we have e.g., x.f<5>;
  TemplateArgumentListInfo TemplateArgs;
  TemplateArgumentListInfo* ExplicitArgs;
  SourceLocation TemplateLoc;
  if (!InjectExplicitTemplateArgs(Cxt, E, TemplateArgs, ExplicitArgs, TemplateLoc))
    return ExprError();

  CXXScopeSpec SS;
  SS.Adopt(QualifierLoc);

  // Note that this will re-do the lookup given transformed args.
  return Cxt.SemaRef.BuildMemberReferenceExpr(
      Base.get(), BaseType, E->getOperatorLoc(), E->isArrow(), SS, 
      TemplateLoc, nullptr, NameInfo, ExplicitArgs, /*Scope=*/nullptr);
}

static ExprResult InjectUnaryTypeExpr(InjectionContext &Cxt, 
                                      UnaryExprOrTypeTraitExpr *E) {
  TypeSourceInfo *TSI = InjectType(Cxt, E->getArgumentTypeInfo());
  if (!TSI)
    return ExprError();
  return Cxt.SemaRef.CreateUnaryExprOrTypeTraitExpr(
      TSI, E->getOperatorLoc(), E->getKind(), E->getSourceRange());
}

static ExprResult InjectUnaryExpr(InjectionContext &Cxt, 
                                  UnaryExprOrTypeTraitExpr *E) {
  if (E->isArgumentType())
    return InjectUnaryTypeExpr(Cxt, E);

  // C++0x [expr.sizeof]p1:
  //   The operand is either an expression, which is an unevaluated operand
  //   [...]
  EnterExpressionEvaluationContext Unevaluated(
      Cxt.SemaRef, Sema::ExpressionEvaluationContext::Unevaluated,
      Sema::ReuseLambdaContextDecl);

  // FIXME: Handle a corner case involving dependent types. See TreeTransform.
  ExprResult SubExpr = InjectExpr(Cxt, E->getArgumentExpr());
  if (SubExpr.isInvalid())
    return ExprError();

  return Cxt.SemaRef.CreateUnaryExprOrTypeTraitExpr(
    SubExpr.get(), E->getOperatorLoc(), E->getKind());
}

static ExprResult InjectUnaryOperator(InjectionContext &Cxt, UnaryOperator *E) {
  ExprResult Sub = InjectExpr(Cxt, E->getSubExpr());
  if (Sub.isInvalid())
    return ExprError();
  return Cxt.SemaRef.BuildUnaryOp(
      nullptr, E->getOperatorLoc(), E->getOpcode(), Sub.get());
}

static ExprResult InjectBinaryOperator(InjectionContext &Cxt, BinaryOperator *E) {
  ExprResult LHS = InjectExpr(Cxt, E->getLHS());
  if (LHS.isInvalid())
    return ExprError();
  ExprResult RHS = InjectExpr(Cxt, E->getRHS());
  if (RHS.isInvalid())
    return ExprError();
  return Cxt.SemaRef.BuildBinOp(
      nullptr, E->getOperatorLoc(), E->getOpcode(), LHS.get(), RHS.get());
}

static ExprResult InjectConditionalOperator(InjectionContext &Cxt, 
                                            ConditionalOperator *E) {
  ExprResult Cond = InjectExpr(Cxt, E->getCond());
  if (Cond.isInvalid())
    return ExprError();

  ExprResult LHS = InjectExpr(Cxt, E->getLHS());
  if (LHS.isInvalid())
    return ExprError();

  ExprResult RHS = InjectExpr(Cxt, E->getRHS());
  if (RHS.isInvalid())
    return ExprError();

  return Cxt.SemaRef.ActOnConditionalOp(
    E->getQuestionLoc(), E->getColonLoc(), Cond.get(), LHS.get(), RHS.get());
}

static ExprResult InjectBinaryConditionalOperator(InjectionContext &Cxt, 
                                                  BinaryConditionalOperator *E) {
  ExprResult Cond = InjectExpr(Cxt, E->getCommon());
  if (Cond.isInvalid())
    return ExprError();

  ExprResult RHS = InjectExpr(Cxt, E->getFalseExpr());
  if (RHS.isInvalid())
    return ExprError();

  return Cxt.SemaRef.ActOnConditionalOp(
    E->getQuestionLoc(), E->getColonLoc(), Cond.get(), nullptr, RHS.get());
}

static ExprResult InjectSubscriptExpr(InjectionContext &Cxt, ArraySubscriptExpr *E) {
  ExprResult LHS = InjectExpr(Cxt, E->getLHS());
  if (LHS.isInvalid())
    return ExprError();

  ExprResult RHS = InjectExpr(Cxt, E->getRHS());
  if (RHS.isInvalid())
    return ExprError();

  SourceLocation Start = E->getLHS()->getLocStart(); // FIXME
  SourceLocation End = E->getRBracketLoc();
  return Cxt.SemaRef.ActOnArraySubscriptExpr(
    /*Scope=*/nullptr, LHS.get(), Start, RHS.get(), End);
}

static ExprResult InjectImplicitCast(InjectionContext &Cxt, ImplicitCastExpr *E) {
  // Implicit casts are eliminated during injection, since they will be 
  // recomputed by semantic analysis.
  return InjectExpr(Cxt, E->getSubExprAsWritten());
}

static ExprResult InjectExplicitCast(InjectionContext &Cxt, CStyleCastExpr *E) {
  TypeSourceInfo *TSI = InjectType(Cxt, E->getTypeInfoAsWritten());
  if (!TSI)
    return ExprError();

  ExprResult SubExpr = InjectExpr(Cxt, E->getSubExprAsWritten());
  if (SubExpr.isInvalid())
    return ExprError();

  return Cxt.SemaRef.BuildCStyleCastExpr(
      E->getLParenLoc(), TSI, E->getRParenLoc(), SubExpr.get());
}

static ExprResult InjectExplicitCast(InjectionContext &Cxt, CXXFunctionalCastExpr *E) {
  TypeSourceInfo *TSI = InjectDeducibleType(Cxt, E->getTypeInfoAsWritten());
  if (!TSI)
    return ExprError();

  ExprResult SubExpr = InjectExpr(Cxt, E->getSubExprAsWritten());
  if (SubExpr.isInvalid())
    return ExprError();

  Expr *Sub = SubExpr.get();
  return Cxt.SemaRef.BuildCXXTypeConstructExpr(
      TSI, E->getLParenLoc(), MultiExprArg(&Sub, 1), E->getRParenLoc());
}

tok::TokenKind GetCastName(Expr *E) {
  switch (E->getStmtClass()) {
  case Stmt::CXXStaticCastExprClass:
    return tok::kw_static_cast;
  case Stmt::CXXDynamicCastExprClass:
    return tok::kw_dynamic_cast;
  case Stmt::CXXReinterpretCastExprClass:
    return tok::kw_reinterpret_cast;
  case Stmt::CXXConstCastExprClass:
    return tok::kw_const_cast;
  default:
    llvm_unreachable("Invalid C++ named cast");
  }
}

ExprResult InjectExplicitCast(InjectionContext &Cxt, CXXNamedCastExpr *E) {
  TypeSourceInfo *TSI = InjectType(Cxt, E->getTypeInfoAsWritten());
  if (!TSI)
    return ExprError();

  ExprResult SubExpr = InjectExpr(Cxt, E->getSubExprAsWritten());
  if (SubExpr.isInvalid())
    return ExprError();

  SourceRange Angles(E->getAngleBrackets());
  SourceRange Parens(Angles.getEnd(), E->getRParenLoc());
  return Cxt.SemaRef.BuildCXXNamedCast(
      E->getOperatorLoc(), GetCastName(E), TSI, SubExpr.get(), Angles, Parens);
}

ExprResult InjectParenListExpr(InjectionContext &Cxt, ParenListExpr *E) {
  SmallVector<Expr*, 4> Inits;
  if (InjectExprs(Cxt, E->getExprs(), E->getNumExprs(), Inits))
    return ExprError();

  return Cxt.SemaRef.ActOnParenListExpr(
      E->getLParenLoc(), E->getRParenLoc(), Inits);
}

ExprResult InjectCXXThisExpr(InjectionContext &Cxt, CXXThisExpr *E) {
  QualType T = Cxt.SemaRef.getCurrentThisType();
  SourceLocation Loc = E->getLocStart();
  Cxt.SemaRef.CheckCXXThisCapture(Loc);
  return new (Cxt.SemaRef.Context) CXXThisExpr(Loc, T, E->isImplicit());
}

ExprResult InjectInitExpr(InjectionContext &Cxt, CXXDefaultInitExpr *E) {
  FieldDecl *Field
    = cast_or_null<FieldDecl>(ResolveDecl(Cxt, E->getField()));
  if (!Field)
    return ExprError();

  return CXXDefaultInitExpr::Create(getASTContext(Cxt), E->getExprLoc(), Field);
}

ExprResult InjectInitExpr(InjectionContext &Cxt, CXXScalarValueInitExpr *E) {
  TypeSourceInfo *TSI = InjectType(Cxt, E->getTypeSourceInfo());
  if (!TSI)
    return ExprError();

  return Cxt.SemaRef.BuildCXXTypeConstructExpr(
      TSI, TSI->getTypeLoc().getEndLoc(), None, E->getRParenLoc());
}

ExprResult InjectInitExpr(InjectionContext &Cxt, CXXStdInitializerListExpr *E) {
  return InjectExpr(Cxt, E->getSubExpr());
}

ExprResult InjectNewExpr(InjectionContext &Cxt, CXXNewExpr *E) {
  // Transform the type that we're allocating
  TypeSourceInfo *AllocTypeInfo = InjectDeducibleType(
      Cxt, E->getAllocatedTypeSourceInfo());
  if (!AllocTypeInfo)
    return ExprError();

  // Transform the size of the array we're allocating (if any).
  ExprResult ArraySize = InjectExpr(Cxt, E->getArraySize());
  if (ArraySize.isInvalid())
    return ExprError();

  // Transform the placement arguments (if any).
  SmallVector<Expr*, 8> PlacementArgs;
  if (!InjectArgs(Cxt, E->getPlacementArgs(), E->getNumPlacementArgs(), PlacementArgs))
    return ExprError();

  // Transform the initializer (if any).
  Expr *OldInit = E->getInitializer();
  ExprResult NewInit;
  if (OldInit)
    NewInit = InjectInit(Cxt, OldInit, true);
  if (NewInit.isInvalid())
    return ExprError();

  // Transform new operator and delete operator.
  FunctionDecl *OperatorNew = nullptr;
  if (E->getOperatorNew()) {
    OperatorNew = cast_or_null<FunctionDecl>(ResolveDecl(Cxt, E->getOperatorNew()));
    if (!OperatorNew)
      return ExprError();
  }

  FunctionDecl *OperatorDelete = nullptr;
  if (E->getOperatorDelete()) {
    OperatorDelete = cast_or_null<FunctionDecl>(ResolveDecl(Cxt, E->getOperatorDelete()));
    if (!OperatorDelete)
      return ExprError();
  }

  QualType AllocType = AllocTypeInfo->getType();
  if (!ArraySize.get()) {
    // If no array size was specified, but the new expression was
    // instantiated with an array type (e.g., "new T" where T is
    // instantiated with "int[4]"), extract the outer bound from the
    // array type as our array size. We do this with constant and
    // dependently-sized array types.
    const ArrayType *AT = getASTContext(Cxt).getAsArrayType(AllocType);
    if (!AT) {
      // Do nothing
    } else if (const ConstantArrayType *CAT = dyn_cast<ConstantArrayType>(AT)) {
      ArraySize = IntegerLiteral::Create(getASTContext(Cxt), CAT->getSize(),
                                         getASTContext(Cxt).getSizeType(),
                                         /*FIXME:*/ E->getLocStart());
      AllocType = CAT->getElementType();
    } else if (const DependentSizedArrayType *DAT = dyn_cast<DependentSizedArrayType>(AT)) {
      if (DAT->getSizeExpr()) {
        ArraySize = DAT->getSizeExpr();
        AllocType = DAT->getElementType();
      }
    }
  }

  return Cxt.SemaRef.BuildCXXNew(
    E->getLocStart(), E->isGlobalNew(), E->getLocStart(), PlacementArgs,
    E->getLocStart(), E->getTypeIdParens(), AllocType, AllocTypeInfo,
    ArraySize.get(), E->getDirectInitRange(), NewInit.get());
}


ExprResult InjectReflectionExpr(InjectionContext &Cxt, ReflectionExpr *E) {
  SourceLocation OpLoc = E->getOperatorLoc();
  if (E->hasExpressionOperand()) {
    ExprResult Expr = InjectExpr(Cxt, E->getExpressionOperand());
    if (Expr.isInvalid())
      return ExprError();
    return Cxt.SemaRef.ActOnCXXReflectExpr(OpLoc, Expr.get());
  }
  TypeSourceInfo *TSI = InjectType(Cxt, E->getTypeOperand());
  if (!TSI)
    return ExprError();
  return Cxt.SemaRef.ActOnCXXReflectExpr(OpLoc, TSI);
}

ExprResult InjectConstantExpr(InjectionContext &Cxt, CXXConstantExpr *E) {
  ExprResult Result = InjectExpr(Cxt, E->getExpression());
  if (Result.isInvalid())
    return ExprError();
  return Cxt.SemaRef.BuildConstantExpression(Result.get());
}

ExprResult InjectCompilerErrorExpr(InjectionContext &Cxt, CompilerErrorExpr *E) {
  ExprResult Message = InjectExpr(Cxt, E->getMessage());
  if (Message.isInvalid())
    return ExprError();
  return Cxt.SemaRef.ActOnCompilerErrorExpr(
      Message.get(), E->getBuiltinLoc(), E->getRParenLoc());
}

ExprResult InjectExpr(InjectionContext &Cxt, Expr *E) {
  if (!E)
    return ExprResult();
  switch (E->getStmtClass()) {
  // case Stmt::PredefinedExpr:
  case Stmt::DeclRefExprClass:
    return InjectDeclRefExpr(Cxt, cast<DeclRefExpr>(E));
  
  case Stmt::IntegerLiteralClass:
  case Stmt::FloatingLiteralClass:
  case Stmt::ImaginaryLiteralClass:
  case Stmt::StringLiteralClass:
  case Stmt::CharacterLiteralClass:
  case Stmt::CXXBoolLiteralExprClass:
  case Stmt::CXXNullPtrLiteralExprClass:
    // Just return the literal.
    return E;
  case Stmt::ParenExprClass:
    return InjectParenExpr(Cxt, cast<ParenExpr>(E));
  case Stmt::UnaryOperatorClass:
    return InjectUnaryOperator(Cxt, cast<UnaryOperator>(E));
  // case Stmt::OffsetOfExprClass:
  case Stmt::UnaryExprOrTypeTraitExprClass:
    return InjectUnaryExpr(Cxt, cast<UnaryExprOrTypeTraitExpr>(E));
  case Stmt::ArraySubscriptExprClass:
    return InjectSubscriptExpr(Cxt, cast<ArraySubscriptExpr>(E));
  case Stmt::CallExprClass:
    return InjectCallExpr(Cxt, cast<CallExpr>(E));
  case Stmt::MemberExprClass:
    return InjectMemberExpr(Cxt, cast<MemberExpr>(E));
  case Stmt::BinaryOperatorClass:
    return InjectBinaryOperator(Cxt, cast<BinaryOperator>(E));
  case Stmt::CompoundAssignOperatorClass:
    return InjectBinaryOperator(Cxt, cast<BinaryOperator>(E));
  case Stmt::ConditionalOperatorClass:
    return InjectConditionalOperator(Cxt, cast<ConditionalOperator>(E));
  case Stmt::BinaryConditionalOperatorClass:
    return InjectBinaryConditionalOperator(Cxt, cast<BinaryConditionalOperator>(E));
  case Stmt::ImplicitCastExprClass:
    return InjectImplicitCast(Cxt, cast<ImplicitCastExpr>(E));
  case Stmt::CStyleCastExprClass:
    return InjectExplicitCast(Cxt, cast<CStyleCastExpr>(E));
  
  // case Stmt::CompoundLiteralExprClass:
  // case Stmt::ExtVectorElementExprClass:
  // case Stmt::InitListExprClass:
  // case Stmt::DesignatedInitExprClass:
  // case Stmt::DesignatedInitUpdateExprClass:
  // case Stmt::ImplicitValueInitExprClass:
  // case Stmt::NoInitExprClass:
  // case Stmt::ArrayInitLoopExprClass:
  // case Stmt::ArrayInitIndexExprClass:
  case Stmt::ParenListExprClass:
    return InjectParenListExpr(Cxt, cast<ParenListExpr>(E));
  // case Stmt::VAArgExprClass:
  // case Stmt::GenericSelectionExprClass:
  // case Stmt::PseudoObjectExprClass:
  
  // Atomic expressions.
  // case Stmt::AtomicExprClass:

  // C++ Expressions.
  case Stmt::CXXOperatorCallExprClass:
    return InjectOperatorCallExpr(Cxt, cast<CXXOperatorCallExpr>(E));
  case Stmt::CXXMemberCallExprClass:
    return InjectCallExpr(Cxt, cast<CXXMemberCallExpr>(E));
  case Stmt::CXXStaticCastExprClass:
  case Stmt::CXXDynamicCastExprClass:
  case Stmt::CXXReinterpretCastExprClass:
  case Stmt::CXXConstCastExprClass:
    return InjectExplicitCast(Cxt, cast<CXXNamedCastExpr>(E));
  case Stmt::CXXFunctionalCastExprClass:
    return InjectExplicitCast(Cxt, cast<CXXFunctionalCastExpr>(E));
  // case Stmt::CXXTypeidExprClass:
  // case Stmt::UserDefinedLiteralClass:
  case Stmt::CXXThisExprClass:
    return InjectCXXThisExpr(Cxt, cast<CXXThisExpr>(E));
  // case Stmt::CXXThrowExprClass:
  // case Stmt::CXXDefaultArgExprClass:
  case Stmt::CXXDefaultInitExprClass:
    return InjectInitExpr(Cxt, cast<CXXDefaultInitExpr>(E));
  case Stmt::CXXScalarValueInitExprClass:
    return InjectInitExpr(Cxt, cast<CXXScalarValueInitExpr>(E));
  case Stmt::CXXStdInitializerListExprClass:
    return InjectInitExpr(Cxt, cast<CXXStdInitializerListExpr>(E));
  case Stmt::CXXNewExprClass:
    return InjectNewExpr(Cxt, cast<CXXNewExpr>(E));
  // case Stmt::CXXDeleteExprClass:
  // case Stmt::CXXPseudoDestructorExprClass:
  // case Stmt::TypeTraitExprClass:
  // case Stmt::ArrayTypeTraitExprClass:
  // case Stmt::ExpressionTraitExprClass:
  case Stmt::DependentScopeDeclRefExprClass:
    return InjectDeclRefExpr(Cxt, cast<DependentScopeDeclRefExpr>(E));
  // case Stmt::CXXConstructExprClass:
  // case Stmt::CXXInheritedCtorInitExprClass:
  // case Stmt::CXXBindTemporaryExprClass:
  // case Stmt::ExprWithCleanupsClass:
  // case Stmt::CXXTemporaryObjectExprClass:
  // case Stmt::CXXUnresolvedConstructExprClass:
  case Stmt::CXXDependentScopeMemberExprClass:
    return InjectMemberExpr(Cxt, cast<CXXDependentScopeMemberExpr>(E));
  // case Stmt::OverloadExprClass:
  // case Stmt::UnresolvedLookupExprClass:
  // case Stmt::UnresolvedMemberExprClass:
  // case Stmt::CXXNoexceptExprClass:
  // case Stmt::PackExpansionExprClass:
  // case Stmt::SizeOfPackExprClass:
  // case Stmt::SubstNonTypeTemplateParmExprClass:
  // case Stmt::SubstNonTypeTemplateParmPackExprClass:
  // case Stmt::FunctionParmPackExprClass:
  // case Stmt::MaterializeTemporaryExprClass:
  // case Stmt::LambdaExprClass:
  // case Stmt::CXXFoldExprClass:
  // case Stmt::CXXDependentIdExprClass:
  // case Stmt::CXXFragmentExprClass:

  // C++ Coroutines TS expressions
  // case Stmt::CoroutineSuspendExprClass:
  // case Stmt::CoawaitExprClass:
  // case Stmt::DependentCoawaitExprClass:
  // case Stmt::CoyieldExprClass:

  // C++ Reflection Expressions
  case Stmt::ReflectionExprClass:
    return InjectReflectionExpr(Cxt, cast<ReflectionExpr>(E));
  // case Stmt::ReflectionTraitExprClass:
  case Stmt::CXXConstantExprClass:
    return InjectConstantExpr(Cxt, cast<CXXConstantExpr>(E));
  case Stmt::CompilerErrorExprClass:
    return InjectCompilerErrorExpr(Cxt, cast<CompilerErrorExpr>(E));

  default:
    E->dump();
    llvm_unreachable("Unknown expression");
  }
  return E;
}

ExprResult InjectExpr(InjectionContext &Cxt, ExprResult E)
{
  if (E.isInvalid())
    return E;
  return InjectExpr(Cxt, E);
}

// Initializers are instantiated like expressions, except that various outer
// layers are stripped.
ExprResult InjectInit(InjectionContext &Cxt, Expr *Init, bool NotCopyInit) {
  if (!Init)
    return Init;

  if (ExprWithCleanups *ExprTemp = dyn_cast<ExprWithCleanups>(Init))
    Init = ExprTemp->getSubExpr();

  if (ArrayInitLoopExpr *AIL = dyn_cast<ArrayInitLoopExpr>(Init))
    Init = AIL->getCommonExpr();

  if (MaterializeTemporaryExpr *MTE = dyn_cast<MaterializeTemporaryExpr>(Init))
    Init = MTE->GetTemporaryExpr();

  while (CXXBindTemporaryExpr *Binder = dyn_cast<CXXBindTemporaryExpr>(Init))
    Init = Binder->getSubExpr();

  if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Init))
    Init = ICE->getSubExprAsWritten();

  if (CXXStdInitializerListExpr *ILE = dyn_cast<CXXStdInitializerListExpr>(Init))
    return InjectInit(Cxt, ILE->getSubExpr(), NotCopyInit);

  // If this is copy-initialization, we only need to reconstruct
  // InitListExprs. Other forms of copy-initialization will be a no-op if
  // the initializer is already the right type.
  CXXConstructExpr *Construct = dyn_cast<CXXConstructExpr>(Init);
  if (!NotCopyInit && !(Construct && Construct->isListInitialization()))
    return InjectExpr(Cxt, Init);

  // Revert value-initialization back to empty parens.
  if (CXXScalarValueInitExpr *VIE = dyn_cast<CXXScalarValueInitExpr>(Init)) {
    SourceRange Parens = VIE->getSourceRange();
    return Cxt.SemaRef.ActOnParenListExpr(Parens.getBegin(), Parens.getEnd(), None);
  }

  // FIXME: We shouldn't build ImplicitValueInitExprs for direct-initialization.
  if (isa<ImplicitValueInitExpr>(Init)) 
    return Cxt.SemaRef.ActOnParenListExpr(SourceLocation(), SourceLocation(), None);

  // Revert initialization by constructor back to a parenthesized or braced list
  // of expressions. Any other form of initializer can just be reused directly.
  if (!Construct || isa<CXXTemporaryObjectExpr>(Construct))
    return InjectExpr(Cxt, Init);

  // If the initialization implicitly converted an initializer list to a
  // std::initializer_list object, unwrap the std::initializer_list too.
  if (Construct && Construct->isStdInitListInitialization())
    return InjectInit(Cxt, Construct->getArg(0), NotCopyInit);

  SmallVector<Expr*, 8> NewArgs;
  if (!InjectExprs(Cxt, Construct->getArgs(), Construct->getNumArgs(), NewArgs))
    return ExprError();

  // If this was list initialization, revert to list form.
  if (Construct->isListInitialization()) {
    QualType ResultType = Construct->getType();
    SourceLocation LBrace = Construct->getLocStart();
    SourceLocation RBrace = Construct->getLocEnd();
    ExprResult Result = Cxt.SemaRef.ActOnInitList(LBrace, NewArgs, RBrace);
    if (Result.isInvalid() || ResultType->isDependentType())
      return Result;

    // Patch in the result type we were given, which may have been computed
    // when the initial InitListExpr was built.
    InitListExpr *ILE = cast<InitListExpr>(Result.get());
    ILE->setType(ResultType);
    return Result;
  }

  // Build a ParenListExpr to represent anything else.
  SourceRange Parens = Construct->getParenOrBraceRange();
  if (Parens.isInvalid()) {
    assert(NewArgs.empty() && "no parens or braces but have direct init");
    return ExprEmpty();
  }
  
  return Cxt.SemaRef.ActOnParenListExpr(Parens.getBegin(), Parens.getEnd(), NewArgs);
}

// Declarations

static bool InjectEnumDefinition(InjectionContext &Cxt, 
                                 EnumDecl *OldEnum,
                                 EnumDecl *NewEnum) {
  SmallVector<Decl*, 4> Enumerators;
  
  EnumConstantDecl *LastConst = nullptr;
  for (auto *OldConst : OldEnum->enumerators()) {
    // The specified value for the enumerator.
    ExprResult Value;
    if (Expr *OldValue = OldConst->getInitExpr()) {
      // The enumerator's value expression is a constant expression.
      EnterExpressionEvaluationContext Unevaluated(
          Cxt.SemaRef, Sema::ExpressionEvaluationContext::ConstantEvaluated);
      Value = InjectExpr(Cxt, OldValue);
    }

    // Drop the initial value and continue.
    bool Invalid = false;
    if (Value.isInvalid()) {
      Value = nullptr;
      Invalid = true;
    }

    // Create the new enum.
    EnumConstantDecl *Const = Cxt.SemaRef.CheckEnumConstant(
        NewEnum, LastConst, OldConst->getLocation(), 
        OldConst->getIdentifier(), Value.get());
    if (!Const) {
      NewEnum->setInvalidDecl();
      continue;
    }

    if (Invalid) {
      Const->setInvalidDecl();
      NewEnum->setInvalidDecl();
    }

    Const->setAccess(OldConst->getAccess());
    NewEnum->addDecl(Const);

    Enumerators.push_back(Const);
    LastConst = Const;
  }

  Cxt.SemaRef.ActOnEnumBody(
      NewEnum->getLocation(), NewEnum->getBraceRange(), NewEnum,
      Enumerators, /*Scope=*/nullptr, /*AttributeList=*/nullptr);

  return !NewEnum->isInvalidDecl();
}

static Decl* InjectEnumDecl(InjectionContext &Cxt, EnumDecl *D) {
  DeclContext *Owner = Cxt.SemaRef.CurContext;

  // FIXME: Transform the name and nested name specifier.

  // FIXME: If there's a previous decl, be sure to link that with this
  // enum.

  // Start by creating the new enumeration.
  EnumDecl *Enum = EnumDecl::Create(
      getASTContext(Cxt), Owner, D->getLocStart(), D->getLocation(), 
      D->getIdentifier(), /*PrevDecl*/nullptr, D->isScoped(), 
      D->isScopedUsingClassTag(), D->isFixed());
  
  if (D->isFixed()) {
    if (TypeSourceInfo *TSI = D->getIntegerTypeSourceInfo()) {
      // If we have type source information for the underlying type, it means it
      // has been explicitly set by the user. Perform substitution on it before
      // moving on.
      TSI = InjectType(Cxt, TSI);
      if (!TSI || Cxt.SemaRef.CheckEnumUnderlyingType(TSI))
        Enum->setIntegerType(Cxt.SemaRef.Context.IntTy);
      else
        Enum->setIntegerTypeSourceInfo(TSI);
    } else {
      assert(!D->getIntegerType()->isDependentType()
             && "Dependent type without type source info");
      Enum->setIntegerType(D->getIntegerType());
    }
  }

  Enum->setAccess(D->getAccess());

  // Forward the mangling number from the template to the instantiated decl.
  getASTContext(Cxt).setManglingNumber(Enum, getASTContext(Cxt).getManglingNumber(D));
  
  // See if the old tag was defined along with a declarator.
  // If it did, mark the new tag as being associated with that declarator.
  if (DeclaratorDecl *DD = getASTContext(Cxt).getDeclaratorForUnnamedTagDecl(D))
    getASTContext(Cxt).addDeclaratorForUnnamedTagDecl(Enum, DD);
  
  // See if the old tag was defined along with a typedef.
  // If it did, mark the new tag as being associated with that typedef.
  if (TypedefNameDecl *TD = getASTContext(Cxt).getTypedefNameForUnnamedTagDecl(D))
    getASTContext(Cxt).addTypedefNameForUnnamedTagDecl(Enum, TD);

  // FIXME: Substitute through the nested name specifier, if any.  
  // if (SubstQualifier(D, Enum))
  //   return nullptr;
  
  Owner->addDecl(Enum);

  // If the enum is defined, inject it.
  EnumDecl *Def = D->getDefinition();
  if (Def == D)
    InjectEnumDefinition(Cxt, D, Enum);

  return D;
}

static Decl* InjectEnumConstantDecl(InjectionContext &Cxt, EnumConstantDecl *D) {
  // NOTE: Enumerators are processed by InjectEnumDefinition.
  llvm_unreachable("Invalid injection");
}


static Decl* InjectTypedefNameDecl(InjectionContext &Cxt, TypedefNameDecl *D) {
  bool Invalid = false;

  DeclContext *Owner = Cxt.SemaRef.CurContext;

  // Transform the type. If this fails, just retain the original, but
  // invalidate the declaration later.
  TypeSourceInfo *TSI = InjectType(Cxt, D->getTypeSourceInfo());
  if (!TSI) {
    TSI = D->getTypeSourceInfo();
    Invalid = true;
  }
  
  // Create the new typedef
  TypedefNameDecl *Typedef;
  if (isa<TypeAliasDecl>(D))
    Typedef = TypeAliasDecl::Create(
        getASTContext(Cxt), Owner, D->getLocStart(), D->getLocation(), 
        D->getIdentifier(), TSI);
  else
    Typedef = TypedefDecl::Create(
        getASTContext(Cxt), Owner, D->getLocStart(), D->getLocation(), 
        D->getIdentifier(), TSI);

  Typedef->setAccess(D->getAccess());
  Typedef->setInvalidDecl(Invalid);
  Owner->addDecl(Typedef);
  
  return Typedef;
}

// Inject the name and the type of a declarator declaration. Sets the
// declaration name info, type, and owner. Returns true if the declarator
// is invalid.
//
// FIXME: If the declarator has a nested names specifier, rebuild that
// also. That potentially modifies the owner of the declaration
static bool InjectDeclarator(InjectionContext &Cxt, 
                             DeclaratorDecl *D, 
                             DeclarationNameInfo &DNI, 
                             TypeSourceInfo *&TSI) {
  bool Invalid = false;

  // Rebuild the name.
  DNI = InjectDeclName(Cxt, D);
  if (!DNI.getName())
    Invalid = true;

  // Rebuild the type.
  TSI = InjectDeclType(Cxt, D);
  if (!TSI) {
    TSI = D->getTypeSourceInfo();
    Invalid = true;
  }

  return Invalid;
}

// Inject the name and the type of a declarator declaration. Sets the
// declaration name info, type, and owner. Returns true if the declarator
// is invalid.
static bool InjectMemberDeclarator(InjectionContext &Cxt, 
                                   DeclaratorDecl *D, 
                                   DeclarationNameInfo &DNI, 
                                   TypeSourceInfo *&TSI, 
                                   CXXRecordDecl *&Owner) {
  bool Invalid = InjectDeclarator(Cxt, D, DNI, TSI);
  Owner = cast<CXXRecordDecl>(Cxt.SemaRef.CurContext);
  return Invalid;
}

static bool InjectVariableInitializer(InjectionContext &Cxt, 
                                      VarDecl *Old,
                                      VarDecl *New) {
  if (Old->getInit()) {
    if (New->isStaticDataMember() && !Old->isOutOfLine())
      Cxt.SemaRef.PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::ConstantEvaluated, Old);
    else
      Cxt.SemaRef.PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::PotentiallyEvaluated, Old);

    // Instantiate the initializer.
    ExprResult Init;
    {
      Sema::ContextRAII SwitchContext(Cxt.SemaRef, New->getDeclContext());
      bool DirectInit = (Old->getInitStyle() == VarDecl::CallInit);
      Init = InjectInit(Cxt, Old->getInit(), DirectInit);
    }
    
    if (!Init.isInvalid()) {
      Expr *InitExpr = Init.get();
      if (New->hasAttr<DLLImportAttr>() &&
          (!InitExpr || 
           !InitExpr->isConstantInitializer(getASTContext(Cxt), false))) {
        // Do not dynamically initialize dllimport variables.
      } else if (InitExpr) {
        Cxt.SemaRef.AddInitializerToDecl(New, InitExpr, Old->isDirectInit());
      } else {
        Cxt.SemaRef.ActOnUninitializedDecl(New);
      }
    } else {
      New->setInvalidDecl();
    }

    Cxt.SemaRef.PopExpressionEvaluationContext();
  } else {
    if (New->isStaticDataMember()) {
      if (!New->isOutOfLine())
        return New;

      // If the declaration inside the class had an initializer, don't add
      // another one to the out-of-line definition.
      if (Old->getFirstDecl()->hasInit())
        return New;
    }

    // We'll add an initializer to a for-range declaration later.
    if (New->isCXXForRangeDecl())
      return New;

    Cxt.SemaRef.ActOnUninitializedDecl(New);
  }
  
  return New;
}

static Decl *InjectVariable(InjectionContext &Cxt, VarDecl *D) {
  DeclContext *Owner = Cxt.SemaRef.CurContext;
  
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  bool Invalid = InjectDeclarator(Cxt, D, DNI, TSI);

  // FIXME: Check for re-declaration.

  VarDecl *Var = VarDecl::Create(
      getASTContext(Cxt), Owner, D->getInnerLocStart(), DNI, TSI->getType(), 
      TSI, D->getStorageClass());

  if (D->isNRVOVariable()) {
    QualType ReturnType = cast<FunctionDecl>(Owner)->getReturnType();
    if (Cxt.SemaRef.isCopyElisionCandidate(ReturnType, Var, false))
      Var->setNRVOVariable(true);
  }

  Owner->addDecl(Var);

  Var->setImplicit(D->isImplicit());
  Var->setInvalidDecl(Invalid);

  // If we are instantiating a local extern declaration, the
  // instantiation belongs lexically to the containing function.
  // If we are instantiating a static data member defined
  // out-of-line, the instantiation will have the same lexical
  // context (which will be a namespace scope) as the template.
  if (D->isLocalExternDecl()) {
    Var->setLocalExternDecl();
    Var->setLexicalDeclContext(Owner);
  } else if (D->isOutOfLine()) {
    Var->setLexicalDeclContext(D->getLexicalDeclContext());
  }
  Var->setTSCSpec(D->getTSCSpec());
  Var->setInitStyle(D->getInitStyle());
  Var->setCXXForRangeDecl(D->isCXXForRangeDecl());
  Var->setConstexpr(D->isConstexpr());
  Var->setInitCapture(D->isInitCapture());
  Var->setPreviousDeclInSameBlockScope(D->isPreviousDeclInSameBlockScope());
  Var->setAccess(D->getAccess());

  if (!D->isStaticDataMember()) {
    if (D->isUsed(false))
      Var->setIsUsed();
    Var->setReferenced(D->isReferenced());
  }

  // FIXME: Instantiate attributes.

  // Forward the mangling number from the template to the instantiated decl.
  getASTContext(Cxt).setManglingNumber(
      Var, getASTContext(Cxt).getManglingNumber(D));
  getASTContext(Cxt).setStaticLocalNumber(
      Var, getASTContext(Cxt).getStaticLocalNumber(D));

  if (D->isInlineSpecified())
    Var->setInlineSpecified();
  else if (D->isInline())
    Var->setImplicitlyInline();

  InjectVariableInitializer(Cxt, D, Var);

  // FIXME: Diagnose un-used declarations here?
  
  return Var;
}

static Decl* InjectParameter(InjectionContext &Cxt, ParmVarDecl *D) {
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  bool Invalid = InjectDeclarator(Cxt, D, DNI, TSI);

  Expr *DefaultArg = nullptr;
  if (D->hasDefaultArg()) {
    ExprResult Default = InjectExpr(Cxt, D->getDefaultArg());
    if (Default.isInvalid())
      Invalid = true;
    else
      DefaultArg = Default.get();
  }

  // Note that the context is overwritten when the parameter is added to
  // a function declaration.
  ParmVarDecl *Parm = ParmVarDecl::Create(
    getASTContext(Cxt), D->getDeclContext(), D->getInnerLocStart(), 
    D->getLocation(), D->getIdentifier(), TSI->getType(), TSI, 
    D->getStorageClass(), DefaultArg);
  
  // FIXME: Under what circumstances do we need to adjust depth and scope?
  Parm->setScopeInfo(D->getFunctionScopeDepth(), D->getFunctionScopeIndex());

  Parm->setInvalidDecl(Invalid);
  return Parm;
}

/// Injects the base specifier Base into Class.
static bool InjectBaseSpecifiers(InjectionContext &Cxt, 
                                 CXXRecordDecl *OldClass,
                                 CXXRecordDecl *NewClass) {
  bool Invalid = false;
  SmallVector<CXXBaseSpecifier*, 4> Bases;
  for (const CXXBaseSpecifier &OldBase : OldClass->bases()) {
    TypeSourceInfo *TSI = InjectType(Cxt, OldBase.getTypeSourceInfo());
    if (!TSI) {
      Invalid = true;
      continue;
    }

    CXXBaseSpecifier *NewBase = Cxt.SemaRef.CheckBaseSpecifier(
        NewClass, OldBase.getSourceRange(), OldBase.isVirtual(), 
        OldBase.getAccessSpecifierAsWritten(), TSI, OldBase.getEllipsisLoc());
    if (!NewBase) {
      Invalid = true;
      continue;
    }

    Bases.push_back(NewBase);
  }

  if (!Invalid && Cxt.SemaRef.AttachBaseSpecifiers(NewClass, Bases))
    Invalid = true;

  // Invalidate the class if necessary.
  NewClass->setInvalidDecl(Invalid);

  return Invalid;
}

static bool InjectClassMembers(InjectionContext &Cxt,
                               CXXRecordDecl *OldClass,
                               CXXRecordDecl *NewClass) {
  for (Decl *OldMember : OldClass->decls()) {
    // Don't transform invalid declarations.
    if (OldMember->isInvalidDecl())
      continue;

    // Don't transform non-members appearing in a class.
    //
    // FIXME: What does it mean to inject friends?
    if (OldMember->getDeclContext() != OldClass)
      continue;
    
    Decl *NewMember = InjectDecl(Cxt, OldMember);
    if (!NewMember)
      NewClass->setInvalidDecl();
  }
  return NewClass->isInvalidDecl();
}

static bool InjectClassDefinition(InjectionContext &Cxt,
                                  CXXRecordDecl *OldClass,
                                  CXXRecordDecl *NewClass) {
  Sema::ContextRAII SwitchContext(Cxt.SemaRef, NewClass);
  Cxt.SemaRef.StartDefinition(NewClass);
  InjectBaseSpecifiers(Cxt, OldClass, NewClass);
  InjectClassMembers(Cxt, OldClass, NewClass);
  Cxt.SemaRef.CompleteDefinition(NewClass);
  return NewClass->isInvalidDecl();
}

static Decl *InjectClassDecl(InjectionContext &Cxt, CXXRecordDecl *D) {
  bool Invalid = false;
  DeclContext *Owner = Cxt.SemaRef.CurContext;

  // FIXME: Do a lookup for previous declarations.

  CXXRecordDecl *Class;
  if (D->isInjectedClassName()) {
    DeclarationName DN = cast<CXXRecordDecl>(Owner)->getDeclName();
    Class = CXXRecordDecl::Create(
        getASTContext(Cxt), D->getTagKind(), Owner, D->getLocStart(), 
        D->getLocation(), DN.getAsIdentifierInfo(), /*PrevDecl=*/nullptr);
  } else {
    DeclarationNameInfo DNI = InjectDeclName(Cxt, D);
    if (!DNI.getName())
      Invalid = true;
    Class = CXXRecordDecl::Create(
        getASTContext(Cxt), D->getTagKind(), Owner, D->getLocStart(), 
        D->getLocation(), DNI.getName().getAsIdentifierInfo(), 
        /*PrevDecl=*/nullptr);
  }

  // FIXME: Inject attributes.

  // FIXME: Propagate other properties?
  Class->setAccess(D->getAccess());
  Class->setImplicit(D->isImplicit());
  Class->setInvalidDecl(Invalid);
  Owner->addDecl(Class);

  if (D->hasDefinition()) 
    InjectClassDefinition(Cxt, D, Class);

  return Class;
}

static Decl *InjectFieldDecl(InjectionContext &Cxt, FieldDecl *D) {
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = InjectMemberDeclarator(Cxt, D, DNI, TSI, Owner);

  // FIXME: Substitute through the bit width.
  Expr *BitWidth = nullptr;

  // Build and check the field.
  FieldDecl *Field = Cxt.SemaRef.CheckFieldDecl(
      DNI.getName(), TSI->getType(), TSI, Owner, D->getLocation(), 
      D->isMutable(), BitWidth, D->getInClassInitStyle(), D->getInnerLocStart(),
      D->getAccess(), nullptr);

  // FIXME: Propagate attributes?

  // FIXME: In general, see VisitFieldDecl in the template instantiatior.
  // There are some interesting cases we probably need to handle.

  // Propagate semantic properties.
  //
  // FIXME: Inherit access as a semantic attribute or trace it through the
  // injection as if parsing?
  Field->setImplicit(D->isImplicit());
  Field->setAccess(D->getAccess());
  Field->setInvalidDecl(Invalid);
  Owner->addDecl(Field);

  // If the field has an initializer, add it to the Fragment so that we
  // can process it later.
  if (D->hasInClassInitializer())
    Cxt.InjectedDefinitions.push_back(InjectedDef(D, Field));

  return Field;
}

static Decl *InjectCXXMethodDecl(InjectionContext &Cxt, CXXMethodDecl *D)
{
  ASTContext &AST = getASTContext(Cxt);
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = InjectMemberDeclarator(Cxt, D, DNI, TSI, Owner);

  // Build the underlying method.
  //
  // FIXME: Should we propagate implicit operators?
  CXXMethodDecl *Method;
  if (CXXConstructorDecl *Ctor = dyn_cast<CXXConstructorDecl>(D)) {
    Method = CXXConstructorDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                        TSI->getType(), TSI,
                                        Ctor->isExplicit(),
                                        Ctor->isInlineSpecified(),
                                        Ctor->isImplicit(), 
                                        Ctor->isConstexpr());
    Method->setRangeEnd(D->getLocEnd());
  } else if (CXXDestructorDecl *Dtor = dyn_cast<CXXDestructorDecl>(D)) {
    Method = CXXDestructorDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                       TSI->getType(), TSI,
                                       Dtor->isInlineSpecified(),
                                       Dtor->isImplicit());
    Method->setRangeEnd(D->getLocEnd());
  } else if (CXXConversionDecl *Conv = dyn_cast<CXXConversionDecl>(D)) {
    Method = CXXConversionDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                       TSI->getType(), TSI,
                                       Conv->isInlineSpecified(),
                                       Conv->isExplicit(), Conv->isConstexpr(),
                                       Conv->getLocEnd());
  } else {
    Method = CXXMethodDecl::Create(AST, Owner, D->getLocStart(), DNI, 
                                   TSI->getType(), TSI, 
                                   D->isStatic() ? SC_Static : SC_None, 
                                   D->isInlineSpecified(), D->isConstexpr(), 
                                   D->getLocEnd());
  }

  // Update the parameters their owning functions.
  FunctionProtoTypeLoc TL = TSI->getTypeLoc().castAs<FunctionProtoTypeLoc>();
  Method->setParams(TL.getParams());
  for (ParmVarDecl *Parm : Method->parameters())
    Parm->setOwningFunction(Method);

  // FIXME: Propagate attributes

  // FIXME: Check for redeclarations

  // Propagate semantic properties.
  //
  // FIXME: Inherit access as a semantic attribute or trace it through the
  // injection as if parsing?
  Method->setImplicit(D->isImplicit());
  Method->setAccess(D->getAccess());
  Method->setDeletedAsWritten(D->isDeletedAsWritten());
  Method->setDefaulted(D->isDefaulted());
  Method->setInvalidDecl(Invalid);
  Owner->addDecl(Method);

  // If the method is has a body, add it to the context so that we can 
  // process it later. Note that deleted/defaulted definitions are just
  // flags processed above.
  if (D->hasBody())
    Cxt.InjectedDefinitions.push_back(InjectedDef(D, Method));

  return Method;
}

static Decl *InjectCXXConstructorDecl(InjectionContext &Cxt, CXXConstructorDecl *D)
{
  return InjectCXXMethodDecl(Cxt, D);
}

static Decl *InjectCXXDestructorDecl(InjectionContext &Cxt, CXXDestructorDecl *D)
{
  return InjectCXXMethodDecl(Cxt, D);
}

static Decl *InjectCXXConversionDecl(InjectionContext &Cxt, CXXConversionDecl *D)
{
  return InjectCXXMethodDecl(Cxt, D);
}

static Decl *InjectAccessSpecDecl(InjectionContext &Cxt, AccessSpecDecl *D)
{
  CXXRecordDecl *Owner = cast<CXXRecordDecl>(Cxt.SemaRef.CurContext);
  return AccessSpecDecl::Create(getASTContext(Cxt), D->getAccess(), Owner,
                                D->getLocation(), D->getColonLoc());
}

static Decl *InjectDeclImpl(InjectionContext &Cxt, Decl *D) {
  switch (D->getKind()) {
  case Decl::Enum:
    return InjectEnumDecl(Cxt, cast<EnumDecl>(D));
  case Decl::EnumConstant:
    return InjectEnumConstantDecl(Cxt, cast<EnumConstantDecl>(D));
  case Decl::Typedef:
  case Decl::TypeAlias:
    return InjectTypedefNameDecl(Cxt, cast<TypedefNameDecl>(D));
  case Decl::Var:
    return InjectVariable(Cxt, cast<VarDecl>(D));
  case Decl::ParmVar:
    return InjectParameter(Cxt, cast<ParmVarDecl>(D));
  case Decl::CXXRecord:
    return InjectClassDecl(Cxt, cast<CXXRecordDecl>(D));
  case Decl::Field:
    return InjectFieldDecl(Cxt, cast<FieldDecl>(D));
  case Decl::CXXMethod:
    return InjectCXXMethodDecl(Cxt, cast<CXXMethodDecl>(D));
  case Decl::CXXConstructor:
    return InjectCXXConstructorDecl(Cxt, cast<CXXConstructorDecl>(D));
  case Decl::CXXDestructor:
    return InjectCXXDestructorDecl(Cxt, cast<CXXDestructorDecl>(D));
  case Decl::CXXConversion:
    return InjectCXXConversionDecl(Cxt, cast<CXXConversionDecl>(D));
  case Decl::AccessSpec:
    return InjectAccessSpecDecl(Cxt, cast<AccessSpecDecl>(D));
  default:
    D->dump();
    llvm_unreachable("unknown declaration");
  }
}

/// \brief Injects a new version of the declaration. Do not use this to
/// resolve references to declarations; use ResolveDecl instead.
Decl *InjectDecl(InjectionContext& Cxt, Decl *D) {
  assert(!Cxt.GetDeclReplacement(D) && "Declaration already injected");
  
  // If the declaration does not appear in the context, then it need
  // not be resolved.
  if (!D->isInFragment())
    return D;

  // Inject the declaration; the result cannot be null.
  Decl *R = InjectDeclImpl(Cxt, D);
  assert(R);

  // Remember the substitution.
  Cxt.AddDeclSubstitution(D, R);
  
  return R;
}

// -------------------------------------------------------------------------- //
// Semantic analysis

// Find variables to capture in the given scope. 
static void FindCapturesInScope(Sema &SemaRef, Scope *S, 
                                SmallVectorImpl<VarDecl *> &Vars) {
  for (Decl *D : S->decls()) {
    if (VarDecl *Var = dyn_cast<VarDecl>(D)) {
      // Only capture locals with initializers. This avoids the capture of
      // a variable defining its own capture.
      if (Var->isLocalVarDeclOrParm() && Var->hasInit())
        Vars.push_back(Var);
    }
  }
}

// Search the scope list for captured variables. When S is null, we're
// applying applying a transformation.
static void FindCaptures(Sema &SemaRef, Scope *S, FunctionDecl *Fn, 
                         SmallVectorImpl<VarDecl *> &Vars) {
  assert(S && "Expected non-null scope");
  while (S && S->getEntity() != Fn) {
    FindCapturesInScope(SemaRef, S, Vars);
    S = S->getParent();
  }
  if (S)
    FindCapturesInScope(SemaRef, S, Vars);
}

/// Construct a reference to each captured value and force an r-value
/// conversion so that we get rvalues during evaluation.
static void ReferenceCaptures(Sema &SemaRef, 
                              SmallVectorImpl<VarDecl *> &Vars,
                              SmallVectorImpl<Expr *> &Refs) {
  Refs.resize(Vars.size());
  std::transform(Vars.begin(), Vars.end(), Refs.begin(), [&](VarDecl *D) {
    Expr *Ref = new (SemaRef.Context) DeclRefExpr(D, false, D->getType(), 
                                                  VK_LValue, D->getLocation());
    return ImplicitCastExpr::Create(SemaRef.Context, D->getType(), 
                                    CK_LValueToRValue, Ref, nullptr, VK_RValue);
  });
}

/// Returns the variable from a captured declaration.
static VarDecl *GetVariableFromCapture(Expr *E)
{
  Expr *Ref = cast<ImplicitCastExpr>(E)->getSubExpr();
  return cast<VarDecl>(cast<DeclRefExpr>(Ref)->getDecl());
}

// Create a placeholder for each captured expression in the scope of the
// fragment. For some captured variable 'v', these have the form:
//
//    constexpr auto v = <opaque>;
//
// These are replaced by their values during injection.
static void CreatePlaceholder(Sema &SemaRef, CXXFragmentDecl *Frag, Expr *E) {
  ValueDecl *Var = GetVariableFromCapture(E);
  SourceLocation IdLoc = Var->getLocation();
  IdentifierInfo *Id = Var->getIdentifier();
  QualType T = SemaRef.Context.DependentTy;
  TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(T);
  VarDecl *Placeholder = VarDecl::Create(SemaRef.Context, Frag, IdLoc, IdLoc, 
                                         Id, T, TSI, SC_Static);
  Placeholder->setConstexpr(true);
  Placeholder->setImplicit(true);
  Placeholder->setInitStyle(VarDecl::CInit);
  Placeholder->setInit(
      new (SemaRef.Context) OpaqueValueExpr(IdLoc, T, VK_RValue));
  Placeholder->setReferenced(true);
  Placeholder->markUsed(SemaRef.Context);
  Frag->addDecl(Placeholder);
}

static void CreatePlaceholders(Sema &SemaRef, CXXFragmentDecl *Frag, 
                               SmallVectorImpl<Expr *> &Captures) {
  std::for_each(Captures.begin(), Captures.end(), [&](Expr *E) {
    CreatePlaceholder(SemaRef, Frag, E);
  });
}

/// Called at the start of a source code fragment to establish the list of
/// automatic variables captured. This is only called by the parser and searches
/// the list of local variables in scope.
void Sema::ActOnCXXFragmentCapture(SmallVectorImpl<Expr *> &Captures) {
  assert(Captures.empty() && "Captures already specified");
  SmallVector<VarDecl *, 8> Vars;
  FindCaptures(*this, CurScope, getCurFunctionDecl(), Vars);
  ReferenceCaptures(*this, Vars, Captures);
}

/// Called at the start of a source code fragment to establish the fragment
/// declaration and placeholders. 
Decl *Sema::ActOnStartCXXFragment(Scope* S, SourceLocation Loc, 
                                  SmallVectorImpl<Expr *> &Captures) {
  CXXFragmentDecl *Fragment = CXXFragmentDecl::Create(Context, CurContext, Loc);
  CreatePlaceholders(*this, Fragment, Captures);
  if (S)
    PushDeclContext(S, Fragment);
  return Fragment;
}

/// Binds the content the fragment declaration. Returns the updated fragment.
/// The Fragment is nullptr if an error occurred during parsing. However,
/// we still need to pop the declaration context.
Decl *Sema::ActOnFinishCXXFragment(Scope *S, Decl *Fragment, Decl *Content) {
  CXXFragmentDecl *FD = nullptr;
  if (Fragment) {
    FD = cast<CXXFragmentDecl>(Fragment);
    FD->setContent(Content);
  }
  
  if (S)
    PopDeclContext();
  
  return FD;
}

/// Builds a new fragment expression.
ExprResult Sema::ActOnCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  return BuildCXXFragmentExpr(Loc, Captures, Fragment);
}

/// \brief Builds a new fragment expression.
/// Consider the following:
///
///   constexpr {
///     int n = 0;
///     auto x = __fragment class { int a, b, c };
///   }
///
/// The type of the expression is a new meta:: class defined, approximately,
/// like this:
///
///   using __base_type = typename($<fragment>); // for exposition
///   
///   struct __fragment_type : base_type
///     // inherit constructors.
///     using base_type::base_type;
///
///     // storage for capture values.
///     int n;
///   };
///
/// TODO: It seems like the base class subobject can be statically initialized
/// as part of a default constructor instead of providing an inherited 
/// constructor and deferring all initialization until evaluation time.
ExprResult Sema::BuildCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  CXXFragmentDecl *FD = cast<CXXFragmentDecl>(Fragment);

  // If the fragment appears in a context that depends on template parameters,
  // then the expression is dependent.
  //
  // FIXME: This is just an approximation of the right answer. In truth, the
  // expression is dependent if the fragment depends on any template parameter
  // in this or any enclosing context.
  if (CurContext->isDependentContext()) {
    return new (Context) CXXFragmentExpr(Context, Loc, Context.DependentTy, 
                                         Captures, FD, nullptr);
  }

  // Build the expression used to the reflection of fragment.
  //
  // TODO: We should be able to compute the type without generating an
  // expression. We're not actually using the expression.
  ExprResult Reflection = BuildDeclReflection(Loc, FD->getContent());
  if (Reflection.isInvalid())
    return ExprError();

  // Generate a fragment expression type.
  //
  // TODO: We currently use the declaration-global Fragment bit to indicate
  // that the type of the expression is (indeed) a reflection of some kind.
  // We might want create the class in the meta:: namespace and rely on only
  // that information.
  CXXRecordDecl *Class = CXXRecordDecl::Create(
      Context, TTK_Class, CurContext, Loc, Loc, nullptr, nullptr);
  Class->setImplicit(true);
  Class->setFragment(true);
  StartDefinition(Class);
  QualType ClassTy = Context.getRecordType(Class);
  TypeSourceInfo *ClassTSI = Context.getTrivialTypeSourceInfo(ClassTy);

  // Build the base class for the fragment type; this is the type of the
  // reflected entity.s
  QualType BaseTy = Reflection.get()->getType();
  TypeSourceInfo *BaseTSI = Context.getTrivialTypeSourceInfo(BaseTy);
  CXXBaseSpecifier* Base = new (Context) CXXBaseSpecifier(
    SourceRange(Loc, Loc), false, true, AS_public, BaseTSI, SourceLocation());
  Class->setBases(&Base, 1);

  // Create a field for each capture.
  SmallVector<FieldDecl *, 4> Fields;
  for (Expr *E : Captures) {
    VarDecl *Var = GetVariableFromCapture(E);
    std::string Name = "__captured_" + Var->getIdentifier()->getName().str();
    IdentifierInfo *Id = &Context.Idents.get(Name);
    TypeSourceInfo *TypeInfo = Context.getTrivialTypeSourceInfo(Var->getType());
    FieldDecl *Field = FieldDecl::Create(
        Context, Class, Loc, Loc, Id, Var->getType(), TypeInfo, nullptr, false, 
        ICIS_NoInit);
    Field->setAccess(AS_public);
    Field->setImplicit(true);
    Fields.push_back(Field);
    Class->addDecl(Field);
  }
  
  // Build a constructor that accepts the generated members.
  DeclarationName Name = Context.DeclarationNames.getCXXConstructorName(
      Context.getCanonicalType(ClassTy));
  DeclarationNameInfo NameInfo(Name, Loc);
  CXXConstructorDecl *Ctor = CXXConstructorDecl::Create(
      Context, Class, Loc, NameInfo, /*Type*/QualType(), /*TInfo=*/nullptr, 
      /*isExplicit=*/true, /*isInline=*/true, /*isImplicitlyDeclared=*/false, 
      /*isConstexpr=*/true);
  Ctor->setAccess(AS_public);

  // Build the function type for said constructor.
  FunctionProtoType::ExtProtoInfo EPI;
  EPI.ExceptionSpec.Type = EST_Unevaluated;
  EPI.ExceptionSpec.SourceDecl = Ctor;
  EPI.ExtInfo = EPI.ExtInfo.withCallingConv(
      Context.getDefaultCallingConvention(/*IsVariadic=*/false,
                                          /*IsCXXMethod=*/true));
  SmallVector<QualType, 4> ArgTypes;
  for (Expr *E : Captures) 
    ArgTypes.push_back(E->getType());
  QualType CtorTy = Context.getFunctionType(Context.VoidTy, ArgTypes, EPI);
  Ctor->setType(CtorTy);

  SmallVector<ParmVarDecl *, 4> Parms;
  for (std::size_t I = 0; I < Captures.size(); ++I) {
    Expr *E = Captures[I];
    VarDecl *Var = GetVariableFromCapture(E);
    std::string Name = "__parm_" + Var->getIdentifier()->getName().str();
    IdentifierInfo* Id = &Context.Idents.get(Name);
    QualType ParmTy = E->getType();
    TypeSourceInfo *TypeInfo = Context.getTrivialTypeSourceInfo(ParmTy);
    ParmVarDecl *Parm = ParmVarDecl::Create(
        Context, Ctor, Loc, Loc, Id, ParmTy, TypeInfo, SC_None, nullptr);
    Parm->setScopeInfo(0, I);
    Parm->setImplicit(true);
    Parms.push_back(Parm);
  }
  Ctor->setParams(Parms);

  // Build constructor initializers.
  std::size_t NumInits = Fields.size() + 1;
  CXXCtorInitializer **Inits = new (Context) CXXCtorInitializer *[NumInits];
  // Build the base initializer.
  {
    SourceLocation EL; // Empty ellipsis.
    Expr *Arg = new (Context) ParenListExpr(Context, Loc, None, Loc);
    Inits[0] = BuildBaseInitializer(BaseTy, BaseTSI, Arg, Class, EL).get();
  }
  // Build member initializers.
  for (std::size_t I = 0; I < Parms.size(); ++I) {
    ParmVarDecl *Parm = Parms[I];
    FieldDecl *Field = Fields[I];
    DeclRefExpr *Ref = new (Context) DeclRefExpr(
        Parm, false, Parm->getType(), VK_LValue, Loc);
    Expr *Arg = new (Context) ParenListExpr(Context, Loc, Ref, Loc);
    Inits[I + 1] = BuildMemberInitializer(Field, Arg, Loc).get();
  }
  Ctor->setNumCtorInitializers(NumInits);
  Ctor->setCtorInitializers(Inits);

  // Build the definition.
  Stmt *Def = new (Context) CompoundStmt(Context, None, Loc, Loc);
  Ctor->setBody(Def);

  Class->addDecl(Ctor);

  CompleteDefinition(Class);

  // Build an expression that that initializes the fragment object.
  Expr *Init;
  if (Captures.size() == 1) {
    CXXConstructExpr *Cast = CXXConstructExpr::Create(
        Context, ClassTy, Loc, Ctor, true, Captures,
        /*HadMultipleCandidates=*/false, /*ListInitialization=*/false, 
        /*StdInitListInitialization=*/false, /*ZeroInitialization=*/false,
        CXXConstructExpr::CK_Complete, SourceRange(Loc, Loc));
    Init = CXXFunctionalCastExpr::Create(
        Context, ClassTy, VK_RValue, ClassTSI, CK_NoOp, Cast, 
        /*Path=*/nullptr, Loc, Loc);
  } else {
    Init = new (Context) CXXTemporaryObjectExpr(
        Context, Ctor, ClassTy, ClassTSI, Captures, SourceRange(Loc, Loc), 
        /*HadMultipleCandidates=*/false, /*ListInitialization=*/false, 
        /*StdInitListInitialization=*/false, /*ZeroInitialization=*/false);
  }

  // Finally, build the fragment expression.
  return new (Context) CXXFragmentExpr(Context, Loc, ClassTy, Captures, FD, Init);
}

/// Returns an injection statement.
StmtResult Sema::ActOnCXXInjectionStmt(SourceLocation Loc, Expr *Reflection) { 
  return BuildCXXInjectionStmt(Loc, Reflection);
}

/// Returns an injection statement.
StmtResult Sema::BuildCXXInjectionStmt(SourceLocation Loc, Expr *Reflection) { 
  // The operand must be a reflection (if non-dependent).
  if (!Reflection->isTypeDependent() && !Reflection->isValueDependent()) {
    if (!isReflectionType(Reflection->getType())) {
      Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
      return StmtError();
    }
  }

  // Perform an lvalue-to-value conversion so that we get an rvalue in
  // evaluation.
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  return new (Context) CXXInjectionStmt(Loc, Reflection);
}

/// An injection declaration injects its fragment members at this point
/// in the program. 
StmtResult Sema::ActOnCXXExtensionStmt(SourceLocation Loc, 
                                       Expr *Target,
                                       Expr *Reflection) { 
  llvm_unreachable("extension not supported");
  // return BuildCXXExtensionStmt(Loc, Target, Reflection);
}

StmtResult Sema::BuildCXXExtensionStmt(SourceLocation Loc, Expr *Target,
                                       Expr *Reflection) { 
  llvm_unreachable("extension not supported");
#if 0
  // Check the glvalue.
  if (!Target->isTypeDependent()) {
    // FIXEM: This isn't strictly *required* since even prvalues are just
    // pointers to a mutable data structure. This is disabled, because the
    // reflection operator returns prvalues, which complicates certain
    // use patterns. For example:
    //
    //    struct C {
    //      constexpr { fill($C); } // Would be an error.
    //    };
    //
    // So, disable this for now.

    // if (!Target->isGLValue()) {
    //   Diag(Target->getExprLoc(), diag::err_extending_rvalue);
    //   return StmtError();
    // }
    
    QualType TargetTy = Context.getCanonicalType(Target->getType());
    if (CXXRecordDecl* Class = TargetTy->getAsCXXRecordDecl()) {
      // FIXME: This isn't the right test. We need to determine during 
      // application if the target satisfies the requirements for extensions.
      // if (!Class->isFragment() || !Class->isBeingDefined()) {
      //   Diag(Target->getExprLoc(), diag::err_extending_declaration);
      //   return StmtError();
      // }
    } else {
      Diag(Target->getExprLoc(), diag::err_extending_non_reflection);
      return StmtError();
    }
  }

  // FIXME: If the reflection is non-dependent, verify that we actually
  // have a reflection.

  // Force an lvalue-to-rvalue conversion.
  if (Target->isGLValue())
    Target = ImplicitCastExpr::Create(Context, Target->getType(), 
                                      CK_LValueToRValue, Target, 
                                      nullptr, VK_RValue);
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  // Build an extension statement that can be evaluated when executed.
  return new (Context) CXXExtensionStmt(Loc, Target, Reflection);
#endif
}

static Decl *
GetDeclFromReflection(Sema &SemaRef, QualType Ty, SourceLocation Loc)
{
  ReflectedConstruct Construct = SemaRef.EvaluateReflection(Ty, Loc);
  Decl *Injection = nullptr;
  if (Type *T = Construct.getAsType()) {
    if (CXXRecordDecl *Class = T->getAsCXXRecordDecl())
      Injection = Class;
  } else
    Injection = Construct.getAsDeclaration();
  if (!Injection) {
    SemaRef.Diag(Loc, diag::err_reflection_not_a_decl);
    return nullptr;
  }
  return Injection;
}

// Not used.
#if 0
static Decl *
GetDeclFromReflection(Sema &SemaRef, Expr *Reflection)
{
  return GetDeclFromReflection(SemaRef, 
                               Reflection->getType(),
                               Reflection->getExprLoc());
}
#endif

/// An injection declaration injects its fragment members at this point
/// in the program. 
Sema::DeclGroupPtrTy Sema::ActOnCXXInjectionDecl(SourceLocation Loc, 
                                                 Expr *Reflection) { 
  llvm_unreachable("injection declarations not supported");
  #if 0
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    Decl *D = CXXInjectionDecl::Create(Context, CurContext, Loc, Reflection);
    // FIXME: Actually use the current access specifier. For now, simply
    // assume that public was meant.
    if (isa<CXXRecordDecl>(CurContext))
      D->setAccess(AS_public);
    CurContext->addDecl(D);
    return DeclGroupPtrTy::make(DeclGroupRef(D));
  }

  // Force an lvalue-to-rvalue conversion.
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  // Get the declaration or fragment to be injected.
  Decl *Injection = GetDeclFromReflection(*this, Reflection);
  if (!Injection)
    return DeclGroupPtrTy();

  // The Injectee is the current context.
  Decl *Injectee = Decl::castFromDeclContext(CurContext);

  // Evaluate the reflection.
  SmallVector<PartialDiagnosticAt, 8> Notes;
  Expr::EvalResult Result;
  Result.Diag = &Notes;
  if (!Reflection->EvaluateAsRValue(Result, Context)) {
    // FIXME: This is not the right error.
    Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
    if (!Notes.empty()) {
      for (const PartialDiagnosticAt &Note : Notes)
        Diag(Note.first, Note.second);
    }
    return DeclGroupPtrTy();
  }

  // FIXME: If this is a fragment without a name, that should probably
  // be an error, right?

  // Always copy the injected declaration.
  QualType Ty = Reflection->getType();
  SmallVector<Decl *, 8> Decls;
  if (!CopyDeclaration(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
    return DeclGroupPtrTy();

  if (Decls.empty()) {
    return DeclGroupPtrTy();
  } else if (Decls.size() == 1) {
    return DeclGroupPtrTy::make(DeclGroupRef(Decls.front()));
  } else {
    DeclGroup *DG = DeclGroup::Create(Context, Decls.data(), Decls.size());
    return DeclGroupPtrTy::make(DeclGroupRef(DG));
  }
  #endif
}

static ClassTemplateSpecializationDecl *ReferencedReflectionClass(Sema &SemaRef, 
                                                                  Expr *E) {
  QualType ExprTy = SemaRef.Context.getCanonicalType(E->getType());
  if (!ExprTy->isRecordType())
    return nullptr;
  CXXRecordDecl* Class = ExprTy->getAsCXXRecordDecl();
  if (!isa<ClassTemplateSpecializationDecl>(Class))
    return nullptr;
  ClassTemplateSpecializationDecl *Spec 
      = cast<ClassTemplateSpecializationDecl>(Class);

  // Make sure that this is actually defined in meta.
  DeclContext* Owner = Class->getDeclContext();
  if (Owner->isInlineNamespace())
    Owner = Owner->getParent();
  if (!Owner->Equals(SemaRef.RequireCppxMetaNamespace(E->getExprLoc()))) 
    return nullptr;
  return Spec;
}

// Returns true if ExprTy refers to either a reflected function or the 
// parameters of a function. If true, Ref is set to the type containing the 
// function's encoded value.
static bool ReferencesFunction(Sema &SemaRef, Expr *E, QualType &RefTy)
{
  auto *Spec = ReferencedReflectionClass(SemaRef, E);
  if (!Spec)
    return false;
  StringRef Name = Spec->getIdentifier()->getName();
  if (Name == "function") {
    RefTy = SemaRef.Context.getTagDeclType(Spec);
    return true;
  }
  if (Name == "reflected_tuple") {
    // Dig out the class containing the info type. It should be:
    //    reflected_tupe<function<X>::parm_info>.
    TemplateArgument First = Spec->getTemplateArgs()[0];
    if (First.getKind() != TemplateArgument::Type)
      return false;
    QualType T = First.getAsType();
    if (!T->isRecordType())
      return false;
    CXXRecordDecl *Class = T->getAsCXXRecordDecl();
    if (Class->getIdentifier()->getName() != "parm_info")
        return false;
    if (!Class->getDeclContext()->isRecord())
      return false;
    Class = cast<CXXRecordDecl>(Class->getDeclContext());
    if (Class->getIdentifier()->getName() != "function" &&
        Class->getIdentifier()->getName() != "method")
      return false;
    RefTy = SemaRef.Context.getTagDeclType(Class);
    return true;
  }

  return false;
}

// Returns true if E refers to a reflected parameter. If true, then Ref is
// set to the type containing the parameter's encoded value.
static bool ReferencesParameter(Sema &SemaRef, Expr *E, QualType &RefTy) {
  auto *Spec = ReferencedReflectionClass(SemaRef, E);
  if (!Spec)
    return false;
  StringRef Name = Spec->getIdentifier()->getName();
  if (Name == "parameter") {
    RefTy = SemaRef.Context.getTagDeclType(Spec);
    return true;
  }
  return false;
}

bool Sema::ActOnCXXInjectedParameter(SourceLocation Loc, Expr *Reflection,
                                     IdentifierInfo *II,
                           SmallVectorImpl<DeclaratorChunk::ParamInfo> &Parms) {
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    // The type is an injected parameter type.
    QualType T = Context.getInjectedParmType(Reflection);
    TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(T);

    // FIXME: Make the constructor accept the type.
    ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                           Context.getTranslationUnitDecl(), 
                                           Loc, Loc, II, T, TSI, SC_None,
                                           nullptr);    
      New->setScopeInfo(CurScope->getFunctionPrototypeDepth(),
                        CurScope->getNextFunctionPrototypeIndex());
    Parms.push_back(DeclaratorChunk::ParamInfo(nullptr, Loc, New));
    return true;
  }

  // If T is meta::function<X> or reflected_tuple<meta::function<X>::parm_info>
  // Then EllipsisLoc must be valid, and we inject all parameters.
  QualType RefTy;
  if (ReferencesFunction(*this, Reflection, RefTy)) {
    ReflectedConstruct C = EvaluateReflection(RefTy, Reflection->getExprLoc());
    FunctionDecl *Fn = cast<FunctionDecl>(C.getAsDeclaration());

    // Clone each parameter, inserting a chunk for the declaration.
    for (ParmVarDecl *Orig : Fn->parameters()) {
      TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(Orig->getType());
      ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                             Context.getTranslationUnitDecl(), 
                                             Orig->getLocStart(), 
                                             Orig->getLocation(), 
                                             Orig->getIdentifier(),
                                             Orig->getType(), TSI, SC_None,
                                             nullptr);
      New->setScopeInfo(CurScope->getFunctionPrototypeDepth(),
                        CurScope->getNextFunctionPrototypeIndex());
      New->setInjected(true);
      Parms.push_back(DeclaratorChunk::ParamInfo(New->getIdentifier(),
                                                 New->getLocation(), New));
    }
    return true;
  }

  // If T is meta::parameter<X>, then we inject that one parameter.
  if (ReferencesParameter(*this, Reflection, RefTy)) {
    // Clone the referenced parameter.
    ReflectedConstruct C = EvaluateReflection(RefTy, Reflection->getExprLoc());
    ParmVarDecl *Orig = cast<ParmVarDecl>(C.getAsDeclaration());
    TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(Orig->getType());
    ParmVarDecl *New = ParmVarDecl::Create(Context, 
                                           Context.getTranslationUnitDecl(),
                                           Orig->getLocStart(), 
                                           Orig->getLocation(), 
                                           Orig->getIdentifier(),
                                           Orig->getType(), TSI, SC_None,
                                           nullptr);
    New->setScopeInfo(CurScope->getFunctionPrototypeDepth(), 
                      CurScope->getNextFunctionPrototypeIndex());
    New->setInjected(true);
    Parms.push_back(DeclaratorChunk::ParamInfo(New->getIdentifier(),
                                               New->getLocation(), New));
    return true;
  }

  // FIXME: Improve diagnostics.
  Diag(Reflection->getExprLoc(), diag::err_compiler_error) << "invalid parameter";
  return false;
}

QualType Sema::BuildInjectedParmType(SourceLocation Loc, Expr *E) {
  if (E->isTypeDependent())
    return Context.getInjectedParmType(E);

  MarkDeclarationsReferencedInExpr(E);
  
  // If T is meta::function<X> or reflected_tuple<meta::function<X>::parm_info>
  // Then EllipsisLoc must be valid, and we inject all parameters.
  QualType RefTy;
  if (ReferencesFunction(*this, E, RefTy)) {
    ReflectedConstruct C = EvaluateReflection(RefTy, E->getExprLoc());
    FunctionDecl *Fn = cast<FunctionDecl>(C.getAsDeclaration());
    return Context.getInjectedParmType(E, Fn->parameters());
  }

  // If T is meta::parameter<X>, then we inject that one parameter.
  if (ReferencesParameter(*this, E, RefTy)) {
    llvm_unreachable("not implemented");
  }

  // FIXME: Improve diagnostics.
  Diag(E->getExprLoc(), diag::err_compiler_error) << "invalid parameter";
  return QualType();
}


// Returns an integer value describing the target context of the injection.
// This correlates to the second %select in err_invalid_injection.
static int DescribeInjectionTarget(DeclContext *DC) {
  if (DC->isFunctionOrMethod())
    return 0;
  else if (DC->isRecord())
    return 1;
  else if (DC->isNamespace())
    return 2;
  else if (DC->isTranslationUnit())
    return 3;
  else
    llvm_unreachable("Invalid injection context");
}

struct TypedValue
{
  QualType Type;
  APValue Value;
};

// Generate an error injecting a declaration of kind SK into the given 
// declaration context. Returns false. Note that SK correlates to the first
// %select in err_invalid_injection.
static bool InvalidInjection(Sema& S, SourceLocation POI, int SK, 
                             DeclContext *DC) {
  S.Diag(POI, diag::err_invalid_injection) << SK << DescribeInjectionTarget(DC);
  return false;
}

// FIXME: This is not particularly good. It would be nice if we didn't have
// to search for ths field.s
static const APValue& GetModifications(const APValue &V, QualType T,
                                       DeclarationName N)
{
  CXXRecordDecl *Class = T->getAsCXXRecordDecl();
  assert(Class && "Expected a class");

  auto Lookup = Class->lookup(N);
  assert(Lookup.size() <= 1 && "Ambiguous reference to traits");
  if (Lookup.empty()) {
    // If we can't find the field, work up recursively.
    if (Class->getNumBases()) {
      CXXBaseSpecifier &B = *Class->bases().begin();
      return GetModifications(V.getStructBase(0), B.getType(), N);
    }
  }
  FieldDecl *F = cast<FieldDecl>(Lookup.front());
  return V.getStructField(F->getFieldIndex());
}

static bool CheckInjectionContexts(Sema &SemaRef, SourceLocation POI,
                                   DeclContext *Injection,
                                   DeclContext *Injectee) {
  if (Injection->isRecord() && !Injectee->isRecord()) {
    InvalidInjection(SemaRef, POI, 1, Injectee);
    return false;
  } else if (Injection->isFileContext() && !Injectee->isFileContext()) {
    InvalidInjection(SemaRef, POI, 0, Injectee);
    return false;
  }
  return true;
}

static bool CheckInjectionKind(Sema &SemaRef, SourceLocation POI,
                               Decl *Injection, DeclContext *Injectee) {
  // Make sure that injection is marginally sane.
  if (VarDecl *Var = dyn_cast<VarDecl>(Injection)) {
    if (Var->hasLocalStorage() && !Injectee->isFunctionOrMethod()) {
      SemaRef.Diag(POI, diag::err_injecting_local_into_invalid_scope)
        << Injectee->isRecord();
      return false;
    }
  }
  return true;
}

/// Inject a fragment into the current context.
bool Sema::InjectFragment(SourceLocation POI, 
                          QualType ReflectionTy, 
                          const APValue &ReflectionVal, 
                          Decl *Injectee, 
                          Decl *Injection) {
  assert(isa<CXXRecordDecl>(Injection) || isa<NamespaceDecl>(Injection));
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);
  DeclContext *InjectionDC = Decl::castToDeclContext(Injection);

  if (!CheckInjectionContexts(*this, POI, InjectionDC, InjecteeDC))
    return false;

  // Extract the captured values for replacement.
  unsigned NumCaptures = ReflectionVal.getStructNumFields();
  ArrayRef<APValue> Captures(None);
  if (NumCaptures) {
    const APValue *First = &ReflectionVal.getStructField(0);
    Captures = ArrayRef<APValue>(First, NumCaptures);
  }

  CXXRecordDecl *Class = ReflectionTy->getAsCXXRecordDecl();
  CXXFragmentDecl *Fragment = cast<CXXFragmentDecl>(Injection->getDeclContext());

  ContextRAII Switch(*this, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // Establish the injection context and register the substitutions.
  InjectionContext *Cxt = new InjectionContext(*this, Fragment, InjecteeDC);
  Cxt->AddDeclSubstitution(Injection, Injectee);
  Cxt->AddPlaceholderSubstitutions(Fragment, Class, Captures);

  // Inject each declaration in the fragment.
  for (Decl *D : InjectionDC->decls()) {
    // Never inject injected class names.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(D))
      if (Class->isInjectedClassName())
        continue;

    llvm::outs() << "BEFORE INJECT\n";
    D->dump();
    
    Decl *R = InjectDecl(*Cxt, D);
    if (!R || R->isInvalidDecl()) {
      // if (R && R->isInvalidDecl()) {
      //   llvm::outs() << "INVALID INJECT\n";
      //   R->dump();
      // }
      Injectee->setInvalidDecl(true);
      continue;
    }

    llvm::outs() << "AFTER INJECT\n";
    R->dump();
  }

  // If we're injecting into a class and have pending definitions, attach
  // those to the class for subsequent analysis. 
  if (CXXRecordDecl *ClassInjectee = dyn_cast<CXXRecordDecl>(Injectee)) {
    if (!Injectee->isInvalidDecl() && !Cxt->InjectedDefinitions.empty()) {
      PendingClassMemberInjections.push_back(Cxt->Detach());
      return true;
    }
  }

  delete Cxt;
  return !Injectee->isInvalidDecl();
}

static Decl *RewriteAsStaticMemberVariable(Sema &SemaRef, 
                                           FieldDecl *D, 
                                           DeclContext *Owner) {
  MultiLevelTemplateArgumentList Args; // Empty arguments for substitution.

  DeclarationNameInfo DNI(D->getDeclName(), D->getLocation());
  DNI = SemaRef.SubstDeclarationNameInfo(DNI, Args);
  if (!DNI.getName())
    return nullptr;

  TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(D->getType());
  TSI = SemaRef.SubstType(TSI, Args, D->getLocation(), DNI.getName());
  if (!TSI)
    return nullptr;
  
  VarDecl *R = VarDecl::Create(SemaRef.Context, Owner, D->getLocation(), DNI,
                               TSI->getType(), TSI, SC_Static);
  R->setAccess(D->getAccess());
  Owner->addDecl(R);

  // Transform the initializer and associated properties of the definition.
  //
  // FIXME: I'm pretty sure that initializer semantics are not being
  // translated incorrectly.
  if (Expr *OldInit = D->getInClassInitializer()) {
    SemaRef.PushExpressionEvaluationContext(
      Sema::ExpressionEvaluationContext::ConstantEvaluated, D);

    ExprResult Init;
    {
      Sema::ContextRAII SwitchContext(SemaRef, R->getDeclContext());
      Init = SemaRef.SubstInitializer(OldInit, Args, false);
    }
    if (!Init.isInvalid()) {
      if (Init.get())
        SemaRef.AddInitializerToDecl(R, Init.get(), false);
      else
        SemaRef.ActOnUninitializedDecl(R);
    } else
      R->setInvalidDecl();
  }

  return R;
}

/// Clone a declaration into the current context.
bool Sema::CopyDeclaration(SourceLocation POI, 
                           QualType ReflectionTy, 
                           const APValue &ReflectionVal,
                           Decl *Injectee, 
                           Decl *Injection) {
  DeclContext *InjectionDC = Injection->getDeclContext();
  Decl *InjectionOwner = Decl::castFromDeclContext(InjectionDC);
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);

  // Don't copy injected class names.
  if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(Injection))
    if (Class->isInjectedClassName())
      return true;

  if (!CheckInjectionContexts(*this, POI, InjectionDC, InjecteeDC))
    return false;

  if (!CheckInjectionKind(*this, POI, Injection, InjecteeDC))
    return false;

  // Set up the injection context. There are no placeholders for copying.
  // Within the copied declaration, references to the enclosing context are 
  // replaced with references to the destination context.
  LocalInstantiationScope Locals(*this);
  InjectionContext InjectionCxt(*this, nullptr, InjecteeDC);
  Sema::InstantiatingTemplate Inst(*this, POI, &InjectionCxt);
  InjectionCxt.AddDeclSubstitution(InjectionOwner, Injectee);

  // Establish injectee as the current context.
  ContextRAII Switch(*this, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // Unpack the modification traits so we can apply them after generating
  // the declaration.
  DeclarationName Name(&Context.Idents.get("mods"));
  const APValue &Traits = GetModifications(ReflectionVal, ReflectionTy, Name);

  enum StorageMod { NoStorage, Static, Automatic, ThreadLocal };
  enum AccessMod { NoAccess, Public, Private, Protected, Default };

  // linkage_kind new_linkage : 2;
  // access_kind new_access : 2;
  // storage_kind new_storage : 2;
  // bool make_constexpr : 1;
  // bool make_virtual : 1;
  // bool make_pure : 1;
  AccessMod Access = (AccessMod)Traits.getStructField(1).getInt().getExtValue();
  StorageMod Storage = (StorageMod)Traits.getStructField(2).getInt().getExtValue();
  bool Constexpr = Traits.getStructField(3).getInt().getExtValue();
  bool Virtual = Traits.getStructField(4).getInt().getExtValue();
  bool Pure = Traits.getStructField(5).getInt().getExtValue();

  assert(Storage != Automatic && "Can't make declarations automatic");
  assert(Storage != ThreadLocal && "Thread local storage not implemented");

  // llvm::outs() << "BEFORE CLONE\n";
  // Injection->dump();
  // Injectee->dump();

  // Build the declaration. If there was a request to make field static, we'll
  // need to build a new declaration.
  Decl* Result;
  if (isa<FieldDecl>(Injection) && Storage == Static) {
    Result = RewriteAsStaticMemberVariable(*this, 
                                           cast<FieldDecl>(Injection), 
                                           InjecteeDC);
  } else {
    MultiLevelTemplateArgumentList Args;
    Result = SubstDecl(Injection, InjecteeDC, Args);
  }
  if (!Result || Result->isInvalidDecl()) {
    Injectee->setInvalidDecl(true);
    return false;
  }
  // llvm::outs() << "AFTER CLONING\n";
  // Result->dump();
  // Injectee->dump();

  // Update access specifiers.
  if (Access) {
    if (!Result->getDeclContext()->isRecord()) {
      Diag(POI, diag::err_modifies_mem_spec_of_non_member) << 0;
      return false;
    }
    switch (Access) {
    case Public:
      Result->setAccess(AS_public);
      break;
    case Private:
      Result->setAccess(AS_private);
      break;
    case Protected:
      Result->setAccess(AS_protected);
      break;
    default:
      llvm_unreachable("Invalid access specifier");
    }
  } else {
    // FIXME: In some cases (nested classes?) member access specifiers
    // are not inherited from the fragments. Force this to be public for now.
    if (isa<CXXRecordDecl>(InjecteeDC)) {
      if (Result->getAccess() == AS_none)
        Result->setAccess(AS_public);
    }
  }

  if (Constexpr) {
    if (VarDecl *Var = dyn_cast<VarDecl>(Result)) {
      Var->setConstexpr(true);
      CheckVariableDeclarationType(Var);
    }
    else if (isa<CXXDestructorDecl>(Result)) {
      Diag(POI, diag::err_declration_cannot_be_made_constexpr);
      return false;
    }
    else if (FunctionDecl *Fn = dyn_cast<FunctionDecl>(Result)) {
      Var->setConstexpr(true);
      CheckConstexprFunctionDecl(Fn);
    } else {
      // Non-members cannot be virtual.
      Diag(POI, diag::err_virtual_non_function);
      return false;
    }
  }

  if (Virtual) {
    if (!isa<CXXMethodDecl>(Result)) {
      Diag(POI, diag::err_virtual_non_function);
      return false;
    }
    
    CXXMethodDecl *Method = cast<CXXMethodDecl>(Result);
    Method->setVirtualAsWritten(true);
  
    if (Pure) {
      // FIXME: Move pure checks up?
      int Err = 0;
      if (Method->isDefaulted()) Err = 2;
      else if (Method->isDeleted()) Err = 3;
      else if (Method->isDefined()) Err = 1;
      if (Err) {
        Diag(POI, diag::err_cannot_make_pure_virtual) << (Err - 1);
        return false;
      }
      CheckPureMethod(Method, Method->getSourceRange());
    }
  }

  // Finally, update the owning context.
  Result->getDeclContext()->updateDecl(Result);

  // Decls.push_back(Result);

  return !Injectee->isInvalidDecl(); 
}

bool Sema::ApplyInjection(SourceLocation POI, InjectionInfo &II) {
  // Get the injection declaration.
  Decl *Injection = GetDeclFromReflection(*this, II.ReflectionType, POI);

  /// Get the injectee declaration. This is either the one specified or
  /// the current context.
  Decl *Injectee = nullptr;
  if (!II.InjecteeType.isNull())
    Injectee = GetDeclFromReflection(*this, II.InjecteeType, POI);
  else
    Injectee = Decl::castFromDeclContext(CurContext);
  if (!Injectee)
    return false;

  // FIXME: Make sure that we can actually apply the injection to the
  // target context. For example, we should only be able to extend fragments
  // or classes currently being defined. We'll need to incorporate the kind
  // of extension operator into the InjectionInfo.

  // Apply the injection operation.
  QualType Ty = II.ReflectionType;
  const APValue &Val = II.ReflectionValue;
  CXXRecordDecl *Class = Ty->getAsCXXRecordDecl();
  if (Class->isFragment())
    return InjectFragment(POI, Ty, Val, Injectee, Injection);
  else
    return CopyDeclaration(POI, Ty, Val, Injectee, Injection);
}

// static void
// PrintDecl(Sema &SemaRef, Decl *D) {
//   PrintingPolicy PP = SemaRef.Context.getPrintingPolicy();
//   PP.TerseOutput = false;
//   D->print(llvm::errs(), PP);
//   llvm::errs() << '\n';
// }

// static void
// PrintType(Sema &SemaRef, Type *T) {
//   if (TagDecl *TD = T->getAsTagDecl())
//     return PrintDecl(SemaRef, TD);
//   PrintingPolicy PP = SemaRef.Context.getPrintingPolicy();
//   QualType QT(T, 0);
//   QT.print(llvm::errs(), PP);
//   llvm::errs() << '\n';
// }

static bool
ApplyDiagnostic(Sema &SemaRef, SourceLocation Loc, const APValue &Arg) {
  ReflectedConstruct R(Arg.getInt().getExtValue());
  if (Decl *D = R.getAsDeclaration()) {
    D->dump();
    // PrintDecl(SemaRef, D);
  }
  else if (Type *T = R.getAsType()) {
    if (TagDecl *TD = T->getAsTagDecl())
      TD->dump();
    else
      T->dump();
    // PrintType(SemaRef, T);
  }
  else
    llvm_unreachable("printing invalid reflection");
  return true;
}

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplyEffects(SourceLocation POI, 
                        SmallVectorImpl<EvalEffect> &Effects) {
  bool Ok = true;
  for (EvalEffect &Effect : Effects) {
    if (Effect.Kind == EvalEffect::InjectionEffect)
      Ok &= ApplyInjection(POI, *Effect.Injection);
    else
      Ok &= ApplyDiagnostic(*this, POI, *Effect.DiagnosticArg);
  }
  return Ok;
}

void Sema::InjectPendingDefinitions() {
  while (!PendingClassMemberInjections.empty()) {
    InjectionContext *Cxt = PendingClassMemberInjections.back();
    PendingClassMemberInjections.pop_back();
    InjectPendingDefinitions(Cxt);
  }
}

void Sema::InjectPendingDefinitions(InjectionContext *Cxt) {
  Cxt->Attach();
  for (InjectedDef Def : Cxt->InjectedDefinitions)
    InjectPendingDefinition(Cxt, Def.Fragment, Def.Injected);
  delete Cxt;
}

void Sema::InjectPendingDefinition(InjectionContext *Cxt, 
                                   Decl *Frag, 
                                   Decl *New) {
  ContextRAII ClassCxt (*this, Frag->getDeclContext());
  if (FieldDecl *OldField = dyn_cast<FieldDecl>(Frag)) {
    FieldDecl *NewField = cast<FieldDecl>(New);
    ExprResult Init = InjectExpr(*Cxt, OldField->getInClassInitializer());
    if (Init.isInvalid())
      NewField->setInvalidDecl();
    else
      NewField->setInClassInitializer(Init.get());
  }
  else if (CXXMethodDecl *OldMethod = dyn_cast<CXXMethodDecl>(Frag)) {
    CXXMethodDecl *NewMethod = cast<CXXMethodDecl>(New);
    ContextRAII MethodCxt (*this, NewMethod);
    StmtResult Body = InjectStmt(*Cxt, OldMethod->getBody());
    if (Body.isInvalid())
      NewMethod->setInvalidDecl();
    else
      NewMethod->setBody(Body.get());
  }
}

Sema::DeclGroupPtrTy Sema::ActOnCXXGeneratedTypeDecl(SourceLocation UsingLoc,
                                                     bool IsClass,
                                                     SourceLocation IdLoc,
                                                     IdentifierInfo *Id,
                                                     Expr *Generator,
                                                     Expr *Reflection) {
  // Create the generated type.
  TagTypeKind TTK = IsClass ? TTK_Class : TTK_Struct;
  CXXRecordDecl *Class = CXXRecordDecl::Create(Context, TTK, CurContext, 
                                               IdLoc, IdLoc, Id);
  Class->setImplicit(true);

  // FIXME: Actually use the current access specifier.
  if (isa<CXXRecordDecl>(CurContext))
    Class->setAccess(AS_public);

  CurContext->addDecl(Class);
  StartDefinition(Class);

  // PushDeclContext(CurScope, Class);
  ContextRAII ClassContext(*this, Class);

  // FIXME: If the reflection (ref) is a fragment DO NOT insert the
  // prototype. A fragment is NOT a type.

  // Insert 'using prototype = typename(ref)'
  IdentifierInfo *ProtoId = &Context.Idents.get("prototype");
  QualType ProtoTy = BuildReflectedType(IdLoc, Reflection);
  TypeSourceInfo *ProtoTSI = Context.getTrivialTypeSourceInfo(ProtoTy);
  Decl *Alias = TypeAliasDecl::Create(Context, Class, IdLoc, IdLoc, 
                                      ProtoId, ProtoTSI);
  Alias->setImplicit(true);
  Alias->setAccess(AS_public);
  Class->addDecl(Alias);

  // Add 'constexpr { <gen>($<id>, <ref>); }' to the class.
  unsigned ScopeFlags;
  Decl *CD = ActOnConstexprDecl(nullptr, UsingLoc, ScopeFlags);
  CD->setImplicit(true);
  CD->setAccess(AS_public);
  
  ActOnStartConstexprDecl(nullptr, CD);
  SourceLocation Loc;

  // Build the expression $<id>.
  QualType ThisType = Context.getRecordType(Class);
  TypeSourceInfo *ThisTypeInfo = Context.getTrivialTypeSourceInfo(ThisType);
  ExprResult Output = ActOnCXXReflectExpr(IdLoc, ThisTypeInfo);

  // Build the call to <gen>($<id>, <ref>)
  Expr *Args[] {Output.get(), Reflection};
  ExprResult Call = ActOnCallExpr(nullptr, Generator, IdLoc, Args, IdLoc);
  Stmt* Body = new (Context) CompoundStmt(Context, Call.get(), IdLoc, IdLoc);

  ActOnFinishConstexprDecl(nullptr, CD, Body);

  CompleteDefinition(Class);
  PopDeclContext();
  
  return DeclGroupPtrTy::make(DeclGroupRef(Class));
}
