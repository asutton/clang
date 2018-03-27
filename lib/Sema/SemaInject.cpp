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

InjectionContext::InjectionContext(Sema &SemaRef, DeclContext *Injectee)
    : SemaRef(SemaRef), Prev(SemaRef.CurrentInjectionContext), 
      Injectee(Injectee) {
  SemaRef.CurrentInjectionContext = this;
}

InjectionContext::InjectionContext(const InjectionContext& Cxt)
  : SemaRef(Cxt.SemaRef), Prev(nullptr), Injectee(Cxt.Injectee),
    DeclSubsts(Cxt.DeclSubsts), PlaceholderSubsts(Cxt.PlaceholderSubsts)
{ }

InjectionContext::~InjectionContext() {
  SemaRef.CurrentInjectionContext = Prev;
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

DeferredGenerationContext::DeferredGenerationContext(Sema &S)
  : SemaRef(S), Prev(S.DeferredGenerations)
{
  SemaRef.DeferredGenerations = this;
}

DeferredGenerationContext::~DeferredGenerationContext()
{
  SemaRef.DeferredGenerations = Prev;
}

// -------------------------------------------------------------------------- //
// Injection

static inline ASTContext& getASTContext(InjectionContext &Cxt) {
  return Cxt.SemaRef.getASTContext();
}

static DeclarationName InjectName(InjectionContext &Cxt, const DeclarationName &N);
static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, NamedDecl *D);

static QualType InjectType(InjectionContext &Cxt, QualType T);
static QualType InjectType(InjectionContext &Cxt, const Type *T);
static TypeSourceInfo *InjectType(InjectionContext &Cxt, TypeSourceInfo *TSI);
static TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, NamedDecl *D);
static TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, DeclaratorDecl *D);

static ExprResult InjectExpr(InjectionContext &Cxt, Expr *E);
static ExprResult InjectExpr(InjectionContext &Cxt, ExprResult E);

static Decl *InjectDecl(InjectionContext &Cxt, Decl *D);

// FIXME: Implement me. In general, we just need to be sure to apply
// transformations to idexprs. Otherwise, these things don't change too
// much.
//
// FIXME: What if the declaration name is qualified?
static DeclarationName InjectName(InjectionContext &Cxt, const DeclarationName &N) {
  return N;
}

static DeclarationNameInfo InjectDeclName(InjectionContext &Cxt, NamedDecl *D) {
  DeclarationName N = InjectName(Cxt, D->getDeclName());
  return DeclarationNameInfo(N, D->getLocation());  
}

static QualType InjectComplexType(InjectionContext &Cxt, const ComplexType *T) {
  QualType Elem = InjectType(Cxt, T->getElementType());
  if (Elem.isNull())
    return QualType();
  return getASTContext(Cxt).getComplexType(Elem);
}

static QualType InjectParenType(InjectionContext &Cxt, const ParenType *T) {
  QualType Inner = InjectType(Cxt, T->getInnerType());
  if (Inner.isNull())
    return QualType();
  return Cxt.SemaRef.BuildParenType(Inner);
}

static QualType InjectPointerType(InjectionContext &Cxt, const PointerType *T) {
  QualType Pointee = InjectType(Cxt, T->getPointeeType());
  if (Pointee.isNull())
    return QualType();
  SourceLocation Loc;
  DeclarationName Name;
  return Cxt.SemaRef.BuildPointerType(Pointee, Loc, Name);
}

static QualType InjectDecayedType(InjectionContext &Cxt, const DecayedType *T) {
  QualType Pointee = InjectType(Cxt, T->getPointeeType());
  if (Pointee.isNull())
    return QualType();
  return getASTContext(Cxt).getDecayedType(Pointee);  
}

static QualType InjectLValueReferenceType(InjectionContext &Cxt, 
                                          const LValueReferenceType *T) {
  QualType Pointee = InjectType(Cxt, T->getPointeeTypeAsWritten());
  if (Pointee.isNull())
    return QualType();
  SourceLocation Loc;
  DeclarationName Name;
  return Cxt.SemaRef.BuildReferenceType(Pointee, true, Loc, Name);
}

static QualType InjectRValueReferenceType(InjectionContext &Cxt, 
                                          const RValueReferenceType *T) {
  QualType Pointee = InjectType(Cxt, T->getPointeeTypeAsWritten());
  if (Pointee.isNull())
    return QualType();
  SourceLocation Loc;
  DeclarationName Name;
  return Cxt.SemaRef.BuildReferenceType(Pointee, false, Loc, Name);
}

static QualType InjectMemberPointerType(InjectionContext &Cxt,
                                        const MemberPointerType *T) {
  QualType Class = InjectType(Cxt, T->getClass());
  if (Class.isNull())
    return QualType();
  QualType Pointee = InjectType(Cxt, T->getPointeeType());
  if (Pointee.isNull())
    return QualType();
  SourceLocation Loc;
  DeclarationName Name;
  return Cxt.SemaRef.BuildMemberPointerType(Pointee, Class, Loc, Name);
}

static QualType InjectArrayType(InjectionContext &Cxt, const ConstantArrayType *T) {
  QualType Elem = InjectType(Cxt, T->getElementType());
  if (Elem.isNull())
    return QualType();
  
  // Build a new literal so we can call BuildArrayType.
  ASTContext &AST = getASTContext(Cxt);
  IntegerLiteral *Size = IntegerLiteral::Create(AST, T->getSize(),
                                                AST.getSizeType(), 
                                                SourceLocation());
  SourceRange Brackets;
  DeclarationName Name;
  return Cxt.SemaRef.BuildArrayType(Elem, T->getSizeModifier(), Size,
                                    T->getIndexTypeCVRQualifiers(), Brackets, 
                                    Name);
}

static QualType InjectArrayType(InjectionContext &Cxt, const VariableArrayType *T) {
  QualType Elem = InjectType(Cxt, T->getElementType());
  if (Elem.isNull())
    return QualType();
  ExprResult Bound = InjectExpr(Cxt, T->getSizeExpr());
  if (Bound.isInvalid())
    return QualType();
  DeclarationName Name;
  return Cxt.SemaRef.BuildArrayType(Elem, T->getSizeModifier(), Bound.get(),
                                    T->getIndexTypeCVRQualifiers(),
                                    T->getBracketsRange(), Name);
}

static QualType InjectArrayType(InjectionContext &Cxt, const IncompleteArrayType *T) {
  QualType Elem = InjectType(Cxt, T->getElementType());
  if (Elem.isNull())
    return QualType();
  SourceRange Brackets;
  DeclarationName Name;
  return Cxt.SemaRef.BuildArrayType(Elem, T->getSizeModifier(), nullptr,
                                    T->getIndexTypeCVRQualifiers(),
                                    Brackets, Name);
}

static QualType InjectArrayType(InjectionContext &Cxt, const DependentSizedArrayType *T) {
  QualType Elem = InjectType(Cxt, T->getElementType());
  if (Elem.isNull())
    return QualType();
  ExprResult Bound = InjectExpr(Cxt, T->getSizeExpr());
  if (Bound.isInvalid())
    return QualType();
  DeclarationName Name;
  return Cxt.SemaRef.BuildArrayType(Elem, T->getSizeModifier(), Bound.get(),
                                    T->getIndexTypeCVRQualifiers(),
                                    T->getBracketsRange(), Name);
}

static QualType InjectFunctionType(InjectionContext &Cxt, const FunctionProtoType *T) {
  QualType Ret = InjectType(Cxt, T->getReturnType());
  if (Ret.isNull())
    return QualType();
  
  SmallVector<QualType, 4> Params(T->getNumParams());
  for (std::size_t I = 0; I < T->getNumParams(); ++I) {
    Params[I] = InjectType(Cxt, T->getParamType(I));
    if (Params[I].isNull())
      return QualType();
  }

  // FIXME: Actually substitute through the prototype. We may have need
  // to substitute through e.g., noexcept specifiers.
  FunctionProtoType::ExtProtoInfo EPI = T->getExtProtoInfo();

  SourceLocation Loc;
  DeclarationName Name;
  return Cxt.SemaRef.BuildFunctionType(Ret, Params, Loc, Name, EPI);
}

static QualType InjectUnresolvedUsingType(InjectionContext &Cxt,
                                          const UnresolvedUsingType *T) {
  Decl *D = InjectDecl(Cxt, T->getDecl());
  if (!D)
    return QualType();
  if (TypeDecl *TD = dyn_cast<TypeDecl>(D))
    return getASTContext(Cxt).getTypeDeclType(TD);
  llvm_unreachable("unknown using type");
}

static QualType InjectTypedefType(InjectionContext &Cxt, const TypedefType *T) {
  Decl *D = InjectDecl(Cxt, T->getDecl());
  if (!D)
    return QualType();
  if (TypedefNameDecl *TD = dyn_cast<TypedefNameDecl>(D))
    return getASTContext(Cxt).getTypedefType(TD);
  llvm_unreachable("unknown typedef type");
}

// FIXME: Implement me. Also, we're probably going to need to use the
// TLB facility to do this "correctly".
QualType InjectType(InjectionContext &Cxt, QualType T) {
  switch (T->getTypeClass()) {
  case Type::Builtin:
    return T;
  case Type::Complex:
    return InjectComplexType(Cxt, cast<ComplexType>(T));
  case Type::Paren:
    return InjectParenType(Cxt, cast<ParenType>(T));
  case Type::Pointer:
    return InjectPointerType(Cxt, cast<PointerType>(T));
  case Type::Decayed:
    return InjectDecayedType(Cxt, cast<DecayedType>(T));
  case Type::LValueReference:
    return InjectLValueReferenceType(Cxt, cast<LValueReferenceType>(T));
  case Type::RValueReference:
    return InjectRValueReferenceType(Cxt, cast<RValueReferenceType>(T));
  case Type::MemberPointer:
    return InjectMemberPointerType(Cxt, cast<MemberPointerType>(T));
  case Type::ConstantArray:
    return InjectArrayType(Cxt, cast<ConstantArrayType>(T));
  case Type::VariableArray:
    return InjectArrayType(Cxt, cast<VariableArrayType>(T));
  case Type::IncompleteArray:
    return InjectArrayType(Cxt, cast<IncompleteArrayType>(T));
  case Type::DependentSizedArray:
    return InjectArrayType(Cxt, cast<DependentSizedArrayType>(T));
  case Type::FunctionProto:
    return InjectFunctionType(Cxt, cast<FunctionProtoType>(T));
  case Type::UnresolvedUsing:
    return InjectUnresolvedUsingType(Cxt, cast<UnresolvedUsingType>(T));
  case Type::Typedef:
    return InjectTypedefType(Cxt, cast<TypedefType>(T));
  default:
    llvm_unreachable("unknown type");
  }
}

QualType InjectType(InjectionContext &Cxt, const Type *T) {
  return InjectType(Cxt, QualType(T, 0));
}

// FIXME: Actually build the TypeLoc correctly.
TypeSourceInfo *InjectType(InjectionContext &Cxt, TypeSourceInfo *TSI)
{
  if (!TSI)
    return TSI;
  QualType T = InjectType(Cxt, TSI->getType());
  if (T.isNull())
    return nullptr;
  TypeLoc TL = TSI->getTypeLoc();
  return getASTContext(Cxt).getTrivialTypeSourceInfo(T, TL.getLocStart());
}

TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, ValueDecl *D) {
  QualType T = InjectType(Cxt, D->getType());
  return getASTContext(Cxt).getTrivialTypeSourceInfo(T);
}

TypeSourceInfo *InjectDeclType(InjectionContext &Cxt, DeclaratorDecl *D) {
  return InjectType(Cxt, D->getTypeSourceInfo());
}

// Expressions

ExprResult InjectExpr(InjectionContext &Cxt, Expr *E) {
  if (!E)
    return ExprError();

  // FIXME: Actually implement this.
  return E;
}

ExprResult InjectExpr(InjectionContext &Cxt, ExprResult E)
{
  if (E.isInvalid())
    return E;
  return InjectExpr(Cxt, E);
}

// Declarations

// Inject the name and the type of a declarator declaration. Sets the
// declaration name info, type, and owner. Returns true if the declarator
// is invalid.
//
// FIXME: If the declarator has a nested names specifier, rebuild that
// also. That potentially modifies the owner of the declaration
static bool InjectMemberDeclarator(InjectionContext &Cxt, 
                                   DeclaratorDecl *D, 
                                   DeclarationNameInfo &DNI, 
                                   TypeSourceInfo *&TSI, 
                                   CXXRecordDecl *&Owner) {
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

  // Determine the owner.
  Owner = cast<CXXRecordDecl>(Cxt.Injectee);

  return Invalid;
}

static Decl *InjectFieldDecl(InjectionContext &Cxt, FieldDecl *D)
{
  DeclarationNameInfo DNI;
  TypeSourceInfo *TSI;
  CXXRecordDecl *Owner;
  bool Invalid = InjectMemberDeclarator(Cxt, D, DNI, TSI, Owner);

  // FIXME: Substitute through the bit width.
  Expr *BitWidth = nullptr;

  // Build and check the field.
  FieldDecl *Field = Cxt.SemaRef.CheckFieldDecl(DNI.getName(), TSI->getType(), 
                                                TSI, Owner, D->getLocation(),
                                                 D->isMutable(), BitWidth,
                                                 D->getInClassInitStyle(),
                                                 D->getInnerLocStart(),
                                                 D->getAccess(),
                                                 nullptr);
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

  // FIXME: Propagate attributes

  // FIXME: Check for redeclarations


  // Propagate semantic properties.
  //
  // FIXME: Inherit access as a semantic attribute or trace it through the
  // injection as if parsing?
  Method->setImplicit(D->isImplicit());
  Method->setAccess(D->getAccess());
  Method->setInvalidDecl(Invalid);
  Owner->addDecl(Method);

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
  CXXRecordDecl *Owner = cast<CXXRecordDecl>(Cxt.Injectee);
  return AccessSpecDecl::Create(getASTContext(Cxt), D->getAccess(), Owner,
                                D->getLocation(), D->getColonLoc());
}


Decl *InjectDecl(InjectionContext& Cxt, Decl *D) {
  // If there is a known substitution, use that.
  if (Decl *R = Cxt.GetDeclReplacement(D))
    return R;

  // If the declaration does not appear in the context, then it need
  // not be resolved.
  if (!D->isInFragment())
    return D;

  switch (D->getKind()) {
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
    llvm_unreachable("unknown declaration");
  }
}

// -------------------------------------------------------------------------- //
// Semantic analysis

// FIXME: Make these members of Sema.
static bool InjectFragment(Sema &SemaRef, SourceLocation POI, 
                           QualType ReflectionTy, const APValue &ReflectionVal, 
                           Decl *Injectee, Decl *Injection, 
                           SmallVectorImpl<Decl *> &Decls);
static bool CopyDeclaration(Sema &SemaRef, SourceLocation POI, 
                            QualType ReflectionTy, const APValue &ReflectionVal, 
                            Decl *Injectee, Decl *Injection, 
                            SmallVectorImpl<Decl *> &Decls);

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

/// Associates the parse state of the class fragment with the fragment itself.
void Sema::ActOnLateParsedClassFragment(Scope *S, void *P) {
  assert(S && isa<CXXFragmentDecl>(S->getEntity()));
  CXXFragmentDecl *Fragment = cast<CXXFragmentDecl>(S->getEntity());
  Fragment->setParsingInfo(P);
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
bool InjectFragment(Sema &SemaRef, SourceLocation POI, QualType ReflectionTy,
                    const APValue &ReflectionVal, Decl *Injectee,
                    Decl *Injection, SmallVectorImpl<Decl *> &Decls) {
  assert(isa<CXXRecordDecl>(Injection) || isa<NamespaceDecl>(Injection));
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);
  DeclContext *InjectionDC = Decl::castToDeclContext(Injection);

  if (!CheckInjectionContexts(SemaRef, POI, InjectionDC, InjecteeDC))
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

  // FIXME: What do we do with the late parsed declarations? We would need
  // to propagate those back toward the parser so that they can be added to
  // the ParsingClass at the point of injection (harder said than done?).

  InjectionContext Ctx(SemaRef, InjecteeDC);
  Sema::ContextRAII Switch(SemaRef, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  for (Decl *D : InjectionDC->decls()) {
    // Never inject injected class names.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(D))
      if (Class->isInjectedClassName())
        continue;

    llvm::outs() << "BEFORE INJECT\n";
    D->dump();
    
    Decl *R = InjectDecl(Ctx, D);
    if (!R || R->isInvalidDecl()) {
      if (R && R->isInvalidDecl()) {
        llvm::outs() << "INVALID INJECT\n";
        R->dump();
      }
      Injectee->setInvalidDecl(true);
      continue;
    }

    llvm::outs() << "AFTER INJECT\n";
    D->dump();

    // If we're injecting into a class, inject members with the 
    // Decls.push_back(R);
  }

  #if 0
  // Set up a bunch of context for the injection. The local instantiation
  // scope stores (for the duration of injection) the new members created
  // by expanding the injection into the current context.
  LocalInstantiationScope Locals(SemaRef);
  InjectionContext InjectionCxt(SemaRef, InjecteeDC);
  Sema::InstantiatingTemplate Inst(SemaRef, POI, &InjectionCxt);
  InjectionCxt.AddDeclSubstitution(Injection, Injectee);
  InjectionCxt.AddPlaceholderSubstitutions(Fragment, Class, Captures);

  // Establish injectee as the current context.
  Sema::ContextRAII Switch(SemaRef, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // llvm::outs() << "BEFORE INJECTION\n";
  // Fragment->dump();

  for (Decl *D : InjectionDC->decls()) {
    // Don't inject injected class names.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(D))
      if (Class->isInjectedClassName())
        continue;

    // llvm::outs() << "BEFORE INJECT\n";
    // D->dump();
    
    MultiLevelTemplateArgumentList Args;
    Decl *R = SemaRef.SubstDecl(D, InjecteeDC, Args);
    if (!R || R->isInvalidDecl()) {
      Injectee->setInvalidDecl(true);
      continue;
    }

    // If we're injecting into a class, inject members with the 

    Decls.push_back(R);
    
    // llvm::outs() << "AFTER INJECT\n";
    // R->dump();
  }

  // llvm::outs() << "FINAL\n";
  // Injectee->dump();
  #endif

  return true;
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
static bool CopyDeclaration(Sema &SemaRef, SourceLocation POI, 
                            QualType ReflectionTy, const APValue &ReflectionVal, 
                            Decl *Injectee, Decl *Injection, 
                            SmallVectorImpl<Decl *> &Decls) {
  DeclContext *InjectionDC = Injection->getDeclContext();
  Decl *InjectionOwner = Decl::castFromDeclContext(InjectionDC);
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);

  // Don't copy injected class names.
  if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(Injection))
    if (Class->isInjectedClassName())
      return true;

  if (!CheckInjectionContexts(SemaRef, POI, InjectionDC, InjecteeDC))
    return false;

  if (!CheckInjectionKind(SemaRef, POI, Injection, InjecteeDC))
    return false;

  // Set up the injection context. There are no placeholders for copying.
  // Within the copied declaration, references to the enclosing context are 
  // replaced with references to the destination context.
  LocalInstantiationScope Locals(SemaRef);
  InjectionContext InjectionCxt(SemaRef, InjecteeDC);
  Sema::InstantiatingTemplate Inst(SemaRef, POI, &InjectionCxt);
  InjectionCxt.AddDeclSubstitution(InjectionOwner, Injectee);

  // Establish injectee as the current context.
  Sema::ContextRAII Switch(SemaRef, InjecteeDC, isa<CXXRecordDecl>(Injectee));

  // Unpack the modification traits so we can apply them after generating
  // the declaration.
  DeclarationName Name(&SemaRef.Context.Idents.get("mods"));
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
    Result = RewriteAsStaticMemberVariable(SemaRef, 
                                           cast<FieldDecl>(Injection), 
                                           InjecteeDC);
  } else {
    MultiLevelTemplateArgumentList Args;
    Result = SemaRef.SubstDecl(Injection, InjecteeDC, Args);
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
      SemaRef.Diag(POI, diag::err_modifies_mem_spec_of_non_member) << 0;
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
      SemaRef.CheckVariableDeclarationType(Var);
    }
    else if (isa<CXXDestructorDecl>(Result)) {
      SemaRef.Diag(POI, diag::err_declration_cannot_be_made_constexpr);
      return false;
    }
    else if (FunctionDecl *Fn = dyn_cast<FunctionDecl>(Result)) {
      Var->setConstexpr(true);
      SemaRef.CheckConstexprFunctionDecl(Fn);
    } else {
      // Non-members cannot be virtual.
      SemaRef.Diag(POI, diag::err_virtual_non_function);
      return false;
    }
  }

  if (Virtual) {
    if (!isa<CXXMethodDecl>(Result)) {
      SemaRef.Diag(POI, diag::err_virtual_non_function);
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
        SemaRef.Diag(POI, diag::err_cannot_make_pure_virtual) << (Err - 1);
        return false;
      }
      SemaRef.CheckPureMethod(Method, Method->getSourceRange());
    }
  }

  // Finally, update the owning context.
  Result->getDeclContext()->updateDecl(Result);

  Decls.push_back(Result);

  return !Injectee->isInvalidDecl(); 
}

static bool
ApplyInjection(Sema &SemaRef, SourceLocation POI, InjectionInfo &II) {
  // Get the injection declaration.
  Decl *Injection = GetDeclFromReflection(SemaRef, II.ReflectionType, POI);

  /// Get the injectee declaration. This is either the one specified or
  /// the current context.
  Decl *Injectee = nullptr;
  if (!II.InjecteeType.isNull())
    Injectee = GetDeclFromReflection(SemaRef, II.InjecteeType, POI);
  else
    Injectee = Decl::castFromDeclContext(SemaRef.CurContext);
  if (!Injectee)
    return false;

  // FIXME: Make sure that we can actually apply the injection to the
  // target context. For example, we should only be able to extend fragments
  // or classes currently being defined. We'll need to incorporate the kind
  // of extension operator into the InjectionInfo.

  // Apply the injection operation.
  QualType Ty = II.ReflectionType;
  const APValue &Val = II.ReflectionValue;
  SmallVector<Decl *, 8> Decls;
  CXXRecordDecl *Class = Ty->getAsCXXRecordDecl();
  if (Class->isFragment())
    return InjectFragment(SemaRef, POI, Ty, Val, Injectee, Injection, Decls);
  else
    return CopyDeclaration(SemaRef, POI, Ty, Val, Injectee, Injection, Decls);
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
      Ok &= ApplyInjection(*this, POI, *Effect.Injection);
    else
      Ok &= ApplyDiagnostic(*this, POI, *Effect.DiagnosticArg);
  }
  return Ok;
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

  DeferredGenerationContext Gens(*this);
  ActOnFinishConstexprDecl(nullptr, CD, Body);

  CompleteDefinition(Class);
  PopDeclContext();
  
  ProcessDeferredGenerations(IdLoc);

  return DeclGroupPtrTy::make(DeclGroupRef(Class));
}

static bool NeedsFnDef(FunctionDecl *O, FunctionDecl *N) {
  return O->isThisDeclarationADefinition() && !N->isThisDeclarationADefinition();
}

void
Sema::ProcessDeferredGenerations(SourceLocation Loc)
{
  if (!DeferredGenerations)
    return;
  
  // If any deferred instantiations were requested, process these now.
  for (DeferredGenerationRequest Req : DeferredGenerations->GetRequests()) {
    // FIXME: We probably need to do the same for variable initializers. 
    // Also, beware that fields may change to vars.
    if (FunctionDecl *OldFn = dyn_cast<FunctionDecl>(Req.Old)) {
      FunctionDecl *NewFn = cast<FunctionDecl>(Req.New);
      if (NeedsFnDef(OldFn, NewFn)) {
        llvm::outs() << "INST DEF\n";
        InstantiateFunctionDefinition(Loc, NewFn, true, true, false);
        OldFn->dump();
        NewFn->dump();
      }
    } else if (CXXRecordDecl *OldClass = dyn_cast<CXXRecordDecl>(Req.Old)) {
      // FIXME: Actually instantiate the class? Use the same logic above,
      // probably.
      CXXRecordDecl *NewClass = cast<CXXRecordDecl>(Req.New);
      assert(OldClass->hasDefinition() ? NewClass->hasDefinition() : true);
    }
  }
}
