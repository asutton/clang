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

InjectionContext::InjectionContext(Sema &SemaRef)
    : SemaRef(SemaRef), Prev(SemaRef.CurrentInjectionContext) {
  SemaRef.CurrentInjectionContext = this;
}

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

// Binds the content the fragment declaration. Returns the updated fragment.
Decl *Sema::ActOnFinishCXXFragment(Scope *S, Decl *Fragment, Decl *Content) {
  CXXFragmentDecl *FD = cast<CXXFragmentDecl>(Fragment);
  FD->setContent(Content);
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

static Decl *
GetDeclFromReflection(Sema &SemaRef, Expr *Reflection)
{
  SourceLocation Loc = Reflection->getExprLoc();
  QualType Ty = Reflection->getType();
  Sema::ReflectedConstruct Construct = SemaRef.EvaluateReflection(Ty, Loc);
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

/// An injection declaration injects its fragment members at this point
/// in the program. 
Sema::DeclGroupPtrTy Sema::ActOnCXXInjectionDecl(SourceLocation Loc, 
                                                 Expr *Reflection) { 
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    Decl *D = CXXInjectionDecl::Create(Context, CurContext, Loc, Reflection);
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

  // Evaluate the injection.
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

  // Apply the corresponding operation. And accumulate the resulting
  // declarations.
  QualType Ty = Reflection->getType();
  CXXRecordDecl *Class = Ty->getAsCXXRecordDecl();
  SmallVector<Decl *, 8> Decls;
  if (Class->isFragment()) {
    if (!InjectFragment(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
      return DeclGroupPtrTy();
  } else {
    if (!CopyDeclaration(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
      return DeclGroupPtrTy();
  }

  if (Decls.empty()) {
    return DeclGroupPtrTy();
  } else if (Decls.size() == 1) {
    return DeclGroupPtrTy::make(DeclGroupRef(Decls.front()));
  } else {
    DeclGroup *DG = DeclGroup::Create(Context, Decls.data(), Decls.size());
    return DeclGroupPtrTy::make(DeclGroupRef(DG));
  }
}

/// An injection declaration injects its fragment members at this point
/// in the program. 
Sema::DeclGroupPtrTy Sema::ActOnCXXExtensionDecl(SourceLocation Loc, 
                                                 Expr *Target,
                                                 Expr *Reflection) { 
  if (Reflection->isTypeDependent() || Reflection->isValueDependent() ||
      Target->isTypeDependent() || Target->isValueDependent()) {
    Decl *D = CXXExtensionDecl::Create(Context, CurContext, Loc, Target, Reflection);
    CurContext->addDecl(D);
    return DeclGroupPtrTy::make(DeclGroupRef(D));
  }

  // Force an lvalue-to-rvalue conversion.
  if (Target->isGLValue())
    Target = ImplicitCastExpr::Create(Context, Target->getType(), 
                                        CK_LValueToRValue, Target, 
                                        nullptr, VK_RValue);
  if (Reflection->isGLValue())
    Reflection = ImplicitCastExpr::Create(Context, Reflection->getType(), 
                                          CK_LValueToRValue, Reflection, 
                                          nullptr, VK_RValue);

  // Get the declaration or fragment to be injected.
  Decl *Injectee = GetDeclFromReflection(*this, Target);
  if (!Injectee)
    return DeclGroupPtrTy();

  // Get the declaration or fragment to be injected.
  Decl *Injection = GetDeclFromReflection(*this, Reflection);
  if (!Injection)
    return DeclGroupPtrTy();

  // FIXME: Do we need to evaluate the reflection? Probably not, we just
  // want to get the declaration so we can inject into it.

  // Evaluate the reflection expression. This may contain captured values or 
  // local modifications to be applied during injection.
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

  // Apply the corresponding operation. And accumulate the resulting
  // declarations.
  QualType Ty = Reflection->getType();
  CXXRecordDecl *Class = Ty->getAsCXXRecordDecl();
  SmallVector<Decl *, 8> Decls;
  if (Class->isFragment()) {
    if (!InjectFragment(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
      return DeclGroupPtrTy();
  } else {
    if (!CopyDeclaration(*this, Loc, Ty, Result.Val, Injectee, Injection, Decls))
      return DeclGroupPtrTy();
  }

  if (Decls.empty()) {
    return DeclGroupPtrTy();
  } else if (Decls.size() == 1) {
    return DeclGroupPtrTy::make(DeclGroupRef(Decls.front()));
  } else {
    DeclGroup *DG = DeclGroup::Create(Context, Decls.data(), Decls.size());
    return DeclGroupPtrTy::make(DeclGroupRef(DG));
  }
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
    New->setScopeInfo(0, Parms.size());
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
      New->setScopeInfo(0, Parms.size());
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
    New->setScopeInfo(0, Parms.size());

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

/// The source code injector is responsible for constructing statements and
/// declarations that are inserted into the AST. The transformation is a simple
/// mapping that replaces one set of names with another. In this regard, it
/// is very much like template instantiation.
class clang::SourceCodeInjector : public TreeTransform<SourceCodeInjector> {
  using BaseType = TreeTransform<SourceCodeInjector>;

  // The parent context of declarations being injected. When injecting a
  // fragment, this is the fragment entity (not the fragment). When injecting 
  // an existing declaration, this is the parent DC of that declaration.
  //
  // This is used to help determine which declarations are members of the
  // current injection and which are not.
  //
  // FIXME: This probably doesn't work the way I'd like for non-fragments.
  // Perhaps it would not be unreasonable to have a fragment injector and
  // a non-fragment injector.
  DeclContext *SourceDC;

  /// The context into which an injection is made.
  ///
  /// This is used to determine if a declaration reference needs to be 
  /// re-resolved, or if it can simply be reused. When the a declaration
  /// is not a member of the target DC...
  DeclContext *DestDC;

public:
  SourceCodeInjector(Sema &SemaRef, DeclContext *Src, DeclContext *Dst)
      : TreeTransform<SourceCodeInjector>(SemaRef), SourceDC(Src), DestDC(Dst),
        ReplacePlaceholders(false) {
    assert((SourceDC ? !isa<CXXFragmentDecl>(SourceDC) : true) && 
           "Source context cannot be a fragment");        
  }

  // When true, declaration references to placeholders are substituted with
  // a constant expression denoting the captured value of the placeholder
  // at the time of evaluation.
  bool ReplacePlaceholders;

  // A mapping of placeholder declarations to their corresponding constant
  // expressions.
  llvm::DenseMap<Decl *, TypedValue> PlaceholderValues;

  // Always rebuild nodes; we're effectively copying from one AST to another.
  bool AlwaysRebuild() const { return true; }

  // Replace the declaration From (in the injected statement or members) with
  // the declaration To (derived from the target context).
  void AddSubstitution(Decl *From, Decl *To) { transformedLocalDecl(From, To); }

  // Register a set of values that will be used to replace the placeholders
  // declared within the fragment.
  void AddReplacements(DeclContext *Fragment, 
                       CXXRecordDecl *ReflectionClass, 
                       ArrayRef<APValue> Captures) {
    assert(isa<CXXFragmentDecl>(Fragment) && "Context is not a fragment");
    auto FieldIter = ReflectionClass->field_begin();
    auto PlaceIter = Fragment->decls_begin();
    for (std::size_t I = 0; I < Captures.size(); ++I) {
      const APValue &Val = Captures[I];
      QualType Ty = (*FieldIter)->getType();

      // TODO: Verify that this is actually a placeholder.
      Decl *Placeholder = *PlaceIter;

      // Register the reference replacement.
      TypedValue TV { Ty, Val };
      PlaceholderValues.try_emplace(Placeholder, TV);

      ++PlaceIter;
      ++FieldIter;
    }

    // Indicate the declrefs to placeholders should be replaced.
    ReplacePlaceholders = true;
  }

  /// Transform the given type. Strip reflected types from the result so that
  /// the resulting AST no longer contains references to a reflected name.
  TypeSourceInfo *TransformInjectedType(TypeSourceInfo *TSI) {
    TSI = TransformType(TSI);
    QualType T = TSI->getType();
    TypeLoc TL = TSI->getTypeLoc();
    if (T->isReflectedType()) {
      T = getSema().Context.getCanonicalType(T);
      TSI = getSema().Context.getTrivialTypeSourceInfo(T, TL.getLocStart());
    }
    return TSI;
  }

  Decl *TransformDecl(Decl *D) {
    return TransformDecl(D->getLocation(), D);
  }

  // If D appears within the fragment being injected, then it needs to be
  // locally transformed.
  Decl *TransformDecl(SourceLocation Loc, Decl *D) {
    if (!D)
      return nullptr;

    // Search for a previous transformation. We need to do this before the
    // context search below.
    auto Known = TransformedLocalDecls.find(D);
    if (Known != TransformedLocalDecls.end()) 
      return Known->second;

    // Only perform a local transformation if D is a member of the current
    // injection. Note that SourceDC is set only if it can have members.
    if (SourceDC) {
      DeclContext *DC = D->getDeclContext();
      while (DC && DC != SourceDC)
        DC = DC->getParent();
      if (DC)
        return TransformLocalDecl(Loc, D);
    }

    if (SourceDC && SourceDC->getParent() == D->getDeclContext()) {
      // This is a reference to a member of the source's enclosing context.
      // For example, it could be a reference to a member variable. For example,
      // consider injecting S::f into a new class (call it T).
      //
      //    struct S {
      //      int a;
      //      int f() { return a; }
      //    };
      //
      // The SourceDC is S::f and the non-member injection is S::a. Because
      // both have the same context, we should interpret this as a request
      // to look up a corresponding member in T (which may fail). In this
      // case, the lookup would be required. If not, we'd have captured a
      // reference to a member variable of another class -- not good.
      //
      // Unfortunately, this is ambiguous. Consider:
      //
      //    struct S {
      //      static int a;
      //      int f() { return a; }
      //    };
      //
      // In this case, both the captured name and new lookup could be valid
      // interpretations of the injection.
      //
      // For now, we always perform a lookup. If lookup fails and D was static
      // then preserve the original declaration (see LookupDecl).
      return LookupDecl(D);
    }

    return D;
  }

  Decl *InjectDecl(Decl *D)
  {
    return TransformLocalDecl(D);
  }

  // Try to find a declaration in the current context having the same
  // identifier as D.
  //
  // FIXME: If we find multiple declarations, perform overload resolution.
  Decl *LookupDecl(Decl *D) {
    NamedDecl *ND = dyn_cast<NamedDecl>(D);
    if (!ND)
      return D;

    DeclarationName Name = ND->getDeclName();
    DeclContext::lookup_result Lookup = DestDC->lookup(Name);

    if (Lookup.empty()) {
      // If lookup fails, but the original declaration was a static member of
      // a class (or a global variable or function in a namespace) then return
      // the original declaration. Otherwise, return nullptr, indicating
      // an error.
      int BadCapture = -1;
      if (CXXMethodDecl *Method = dyn_cast<CXXMethodDecl>(ND)) {
        if (!Method->isInstance())
          BadCapture = 0;
      } else if (FieldDecl *Field = dyn_cast<FieldDecl>(ND)) {
        BadCapture = 1;
      }
      if (BadCapture >= 0)
        getSema().Diag(D->getLocation(), diag::err_capture_non_static) 
            << BadCapture;
      return D;
    }

    if (Lookup.size() > 1)
      llvm_unreachable("Injection requires overload resolution");

    return Lookup.front();
  }

  // Transform the definition, unless it's member function definition. Then
  // defer that until the end of the class.
  void TransformFunctionDefinition(FunctionDecl *D, FunctionDecl *R) {
      BaseType::TransformFunctionDefinition(D, R);
  }

  /// Transform a definition that was previously pending.
  void TransformPendingDefinition(FunctionDecl *D, FunctionDecl *R) {
      BaseType::TransformFunctionDefinition(D, R);    
  }

  Decl* RewriteAsStaticMember(Decl *D) {
    if (CXXMethodDecl *Method = dyn_cast<CXXMethodDecl>(D))
      return RewriteAsStaticMemberFunction(Method);
    if (FieldDecl *Field = dyn_cast<FieldDecl>(D))
      return RewriteAsStaticMemberVariable(Field);
    else
      return InjectDecl(D);
  }

  // Given a field, rewrite this as a static member.
  Decl *RewriteAsStaticMemberVariable(FieldDecl *D) {
    DeclContext *Owner = getSema().CurContext;

    DeclarationNameInfo DNI(D->getDeclName(), D->getLocation());
    DNI = TransformDeclarationNameInfo(DNI);
    if (!DNI.getName())
      return nullptr;

    TypeSourceInfo *TSI = TransformTypeCanonical(getDerived(), D);
    if (!TSI)
      return nullptr;
    
    VarDecl *R 
      = VarDecl::Create(getSema().Context, Owner, D->getLocation(), DNI,
                        TSI->getType(), TSI, SC_Static);
    transformedLocalDecl(D, R);

    // FIXME: What attributes of a field can we really transform here.
    // Note that the library should actually apply some limitations (e.g.,
    // don't make mutable members static?).
    Owner->addDecl(R);

    // Transform the initializer and associated properties of the definition.
    //
    // FIXME: I'm pretty sure that initializer semantics are not being
    // translated incorrectly.
    if (Expr *OldInit = D->getInClassInitializer()) {
      getSema().PushExpressionEvaluationContext(
        Sema::ExpressionEvaluationContext::ConstantEvaluated, D);

      ExprResult Init;
      {
        Sema::ContextRAII SwitchContext(SemaRef, R->getDeclContext());
        Init = getDerived().TransformInitializer(OldInit, false);
      }
      if (!Init.isInvalid()) {
        if (Init.get())
          getSema().AddInitializerToDecl(R, Init.get(), false);
        else
          getSema().ActOnUninitializedDecl(R);
      } else
        R->setInvalidDecl();
    }

    return R;
  }

  // Given a field, rewrite this as a static member.
  Decl *RewriteAsStaticMemberFunction(CXXMethodDecl *D) {
    return TransformLocalCXXMethodDecl(D, true);
  }

  // If we have a substitution for the template parameter type apply
  // that here.
  QualType TransformTemplateTypeParmType(TypeLocBuilder &TLB, 
                                         TemplateTypeParmTypeLoc TL) {
    if (Decl *D = TL.getDecl()) {
      auto Known = TransformedLocalDecls.find(D);
      if (Known != TransformedLocalDecls.end()) {
        Decl *R = Known->second;
        assert(isa<TagDecl>(R) && "Invalid template parameter substitution");
        QualType T = SemaRef.Context.getTagDeclType(cast<TagDecl>(R));
        TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(T);
        return TransformType(TLB, TSI->getTypeLoc());
      }
    }
    return BaseType::TransformTemplateTypeParmType(TLB, TL);
  }

  // If this is a reference to a placeholder variable.
  ExprResult TransformDeclRefExpr(DeclRefExpr *E) {
    if (!ReplacePlaceholders)
      return BaseType::TransformDeclRefExpr(E);

    auto Known = PlaceholderValues.find(E->getDecl());
    if (Known != PlaceholderValues.end()) {
      // Build a new constant expression as the replacement. The source
      // expression is opaque since the actual declaration isn't part of
      // the output AST (but we might want it as context later -- makes
      // pretty printing more elegant).
      const TypedValue &TV = Known->second;
      Expr *O = new (SemaRef.Context) OpaqueValueExpr(E->getLocation(), 
                                                      TV.Type, VK_RValue, 
                                                      OK_Ordinary, E);
      return new (SemaRef.Context) CXXConstantExpr(O, TV.Value);
    }

    return BaseType::TransformDeclRefExpr(E);
  }
};

SourceCodeInjector &Sema::MakeInjector(DeclContext *Src, DeclContext *Dst) {
  SourceCodeInjector *Injector = new SourceCodeInjector(*this, Src, Dst);
  Injectors.push_back(Injector);
  return *Injector;
}

void Sema::DestroyInjectors() {
  for (SourceCodeInjector *I : Injectors)
    delete I;
}

/// Returns the transformed statement S. 
bool Sema::InjectBlockStatements(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isFunctionOrMethod())
    return InvalidInjection(*this, POI, 0, CurContext);

  // Note that we are instantiating a template.
  // InstantiatingTemplate Inst(*this, POI);

  /*
  SourceCodeInjector Injector(*this, S->getInjectionContext());

  // Transform each statement in turn. Note that we build build a compound
  // statement from all injected statements at the point of injection.
  CompoundStmt *Block = S->getBlockFragment();
  for (Stmt *B : Block->body()) {
    StmtResult R = Injector.TransformStmt(B);
    if (R.isInvalid())
      return false;
    InjectedStmts.push_back(R.get());
  }
  */
  
  return true;
}



// Called after a metaprogram has been evaluated to apply the resulting
// injections as source code.
bool Sema::InjectClassMembers(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isRecord())
    return InvalidInjection(*this, POI, 1, CurContext);

#if 0
  // Note that we are instantiating a template.
  InstantiatingTemplate Inst(*this, POI);

  const CXXInjectionStmt *IS = cast<CXXInjectionStmt>(II.Injection);
  CXXRecordDecl *Target = cast<CXXRecordDecl>(CurContext);
  CXXRecordDecl *Source = IS->getClassFragment();

  // Inject the source fragment into the the target, replacing references to
  // the source with those of the target.
  ContextRAII SavedContext(*this, Target);
  SourceCodeInjector Injector(*this, Source);
  Injector.AddSubstitution(Source, Target);

  // Generate replacements for placeholders.
  auto DeclIter = Source->decls_begin();
  auto DeclEnd = Source->decls_end();
  const SmallVectorImpl<APValue> &Values = II.CaptureValues;
  ReplacePlaceholders(*this, Injector, IS, Values, DeclIter, DeclEnd);

  // Inject the remaining declarations.
  while (DeclIter != DeclEnd) {
    Decl *Member = *DeclIter;

    if (!Injector.TransformLocalDecl(Member))
      Target->setInvalidDecl(true);

    ++DeclIter;
  }

  return !Target->isInvalidDecl();
#endif
  return true;
}

bool Sema::InjectNamespaceMembers(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isFileContext())
    return InvalidInjection(*this, POI, 2, CurContext);

  // Note that we are instantiating a template.
  // InstantiatingTemplate Inst(*this, POI);

  /*
  NamespaceDecl *Source = D->getNamespaceFragment();
  SourceCodeInjector Injector(*this, Source);
  if (CurContext->isNamespace())
    Injector.AddSubstitution(Source, cast<NamespaceDecl>(CurContext));
  else
    Injector.AddSubstitution(Source, cast<TranslationUnitDecl>(CurContext));

  // Transform each declaration in turn.
  //
  // FIXME: Notify AST observers of new top-level declarations?
  for (Decl *Member : Source->decls())
    Injector.TransformDecl(Member);
  */

  return true;
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

  // Set up a bunch of context for the injection. The local instantiation
  // scope stores (for the duration of injection) the new members created
  // by expanding the injection into the current context.
  LocalInstantiationScope Locals(SemaRef);
  InjectionContext InjectionCxt(SemaRef);
  Sema::InstantiatingTemplate Inst(SemaRef, POI, &InjectionCxt);
  InjectionCxt.AddDeclSubstitution(Injection, Injectee);
  InjectionCxt.AddPlaceholderSubstitutions(Fragment, Class, Captures);

  // llvm::outs() << "=============================================\n";
  // llvm::outs() << "INJECTING\n";
  // Fragment->dump();

  for (Decl *D : InjectionDC->decls()) {
    // Don't inject injected class names.
    if (CXXRecordDecl *Class = dyn_cast<CXXRecordDecl>(D))
      if (Class->isInjectedClassName())
        continue;

    // llvm::outs() << "BEFORE\n";
    // D->dump();
    
    MultiLevelTemplateArgumentList Args;
    Decl *R = SemaRef.SubstDecl(D, InjecteeDC, Args);
    if (!R || R->isInvalidDecl()) {
      Injectee->setInvalidDecl(true);
      continue;
    }

    Decls.push_back(R);
    
    // llvm::outs() << "AFTER\n";
    // R->dump();
  }

  // llvm::outs() << "*************************************\n";
  // llvm::outs() << "FINAL\n";
  // Injectee->dump();

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
  DeclContext *InjecteeDC = Decl::castToDeclContext(Injectee);

  if (!CheckInjectionContexts(SemaRef, POI, InjectionDC, InjecteeDC))
    return false;

  if (!CheckInjectionKind(SemaRef, POI, Injection, InjecteeDC))
    return false;

  // Set up the injection context. There are no placeholders for copying.
  // Note that we also don't need a local instantiation scope at this
  // level. However, nested substitutions may require one.
  InjectionContext InjectionCxt(SemaRef);
  Sema::InstantiatingTemplate Inst(SemaRef, POI, &InjectionCxt);
  InjectionCxt.AddDeclSubstitution(Injection, Injectee);

  // // Configure the injection. Within the injected declaration, references
  // // to the enclosing context are replaced with references to the destination
  // // context.
  // SourceCodeInjector &Injector = SemaRef.MakeInjector(SourceDC, InjecteeDC);
  // Injector.AddSubstitution(Decl::castFromDeclContext(InjectionDC), Injectee);

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

  CXXRecordDecl *Class = nullptr;
  if (isa<CXXRecordDecl>(Injectee))
    // The injection site is a class and the injection is a member. We need
    // to establish the pending member transformation context for the receiving
    // class.
    Class = cast<CXXRecordDecl>(Injectee);
  else if (isa<CXXRecordDecl>(Injection))
    // The injection itself is a class that may have members whose definitions
    // will be transformed after completion. Establish the transformation
    // context for the injection itself.
    Class = cast<CXXRecordDecl>(Injection);

  // Build the declaration. If there was a request to make field static, we'll
  // need to build a new declaration.
  // llvm::outs() << "BEFORE\n";
  // Injection->dump();
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
  // llvm::outs() << "AFTER: " << Result->getDeclContext() << '\n';
  // Result->dump();
  // Decl::castFromDeclContext(Result->getDeclContext())->dump();

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

  return Injectee->isInvalidDecl(); 
}

static bool
ApplyInjection(Sema &SemaRef, SourceLocation POI, Sema::InjectionInfo &II) {
  // Get the declaration or fragment to be injected. 
  Sema::ReflectedConstruct Construct = 
      SemaRef.EvaluateReflection(II.ReflectionType, POI);
  Decl *Injection = nullptr;
  if (Type *T = Construct.getAsType()) {
    if (CXXRecordDecl *Class = T->getAsCXXRecordDecl())
      Injection = Class;
  } else
    Injection = Construct.getAsDeclaration();
  if (!Injection) {
    SemaRef.Diag(POI, diag::err_reflection_not_a_decl);
    return false;
  }

  /// The injectee is the current context.
  Decl *Injectee = Decl::castFromDeclContext(SemaRef.CurContext);

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

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplySourceCodeModifications(SourceLocation POI, 
                                   SmallVectorImpl<InjectionInfo> &Injections) {
  bool Ok = true;
  for (InjectionInfo &II : Injections)
    Ok &= ApplyInjection(*this, POI, II);
  return Ok;
}


/// Copy, by way of transforming, the members of the given C++ metaclass into
/// the target class.
///
/// The \p Fields parameter is used to store injected fields for subsequent
/// analysis by ActOnFields().
///
/// Note that this is always called within the scope of the receiving class,
/// as if the declarations were being written in-place.
void Sema::ApplyMetaclass(MetaclassDecl *Meta, 
                          CXXRecordDecl *ProtoArg,
                          CXXRecordDecl *Final,
                          SmallVectorImpl<Decl *> &Fields) {
  
#if 0
  CXXRecordDecl *Def = Meta->getDefinition();

  // Recursively inject base classes.
  for (CXXBaseSpecifier &B : Def->bases()) {
    QualType T = B.getType();
    CXXRecordDecl *BaseClass = T->getAsCXXRecordDecl();
    assert(BaseClass->isMetaclassDefinition() && 
           "Metaclass inheritance from regular class");
    MetaclassDecl *BaseMeta = cast<MetaclassDecl>(BaseClass->getDeclContext());
    ApplyMetaclass(BaseMeta, ProtoArg, Final, Fields);
  }

  // Note that we are synthesizing code.
  //
  // FIXME: The point of instantiation/injection is incorrect.
  InstantiatingTemplate Inst(*this, Final->getLocation());
  ContextRAII SavedContext(*this, Final);
  SourceCodeInjector& Injector = MakeInjector(Def, Final);

  // When injecting replace references to the metaclass definition with
  // references to the final class.
  Injector.AddSubstitution(Def, Final);

  // Also replace references to the prototype parameter with references to
  // the final class.
  Decl *ProtoParm = *Def->decls_begin();
  assert(isa<TemplateTypeParmDecl>(ProtoParm) && "Expected prototype");
  Injector.AddSubstitution(ProtoParm, ProtoArg);

  // Propagate attributes on a metaclass to the final class.
  Injector.TransformAttributes(Def, Final);

  // Inject each member in turn.
  for (Decl *D : Def->decls()) {
    // Don't transform the prototype parameter. 
    //
    // FIXME: Handle this separately by creating a type alias in the
    // final class.
    if (D == ProtoParm)
      continue;

    Decl *R = Injector.TransformLocalDecl(D);
    if (!R) 
      Final->setInvalidDecl(true);
  }
  
  if (Final->isInvalidDecl())
    return;
#endif
}

