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
#include "clang/Sema/SemaInternal.h"

using namespace clang;
using namespace sema;

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
  assert(S && "Walked off of scope stack");
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
  Class->startDefinition();
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

  Class->completeDefinition();

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
  CXXFragmentExpr *Result = new (Context) CXXFragmentExpr(Context, Loc, ClassTy, 
                                                          Captures, FD, Init);
  return Result;
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
Sema::DeclGroupPtrTy Sema::ActOnCXXInjectionDecl(SourceLocation Loc, 
                                                 Expr *Reflection) { 
  if (Reflection->isTypeDependent() || Reflection->isValueDependent()) {
    // Preserve the declaration until instantiation.
    Decl *D = CXXInjectionDecl::Create(Context, CurContext, Loc, Reflection);
    return DeclGroupPtrTy::make(DeclGroupRef(D));
  }

  // The operand must be a reflection.
  QualType T = Reflection->getType();
  if (!isReflectionType(T)) {
    Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
    return DeclGroupPtrTy();
  }

  // FIXME: C must either be a class or namespace. Inject members as
  // appropriate.
  ReflectedConstruct C = EvaluateReflection(Reflection);
  if (Decl *D = C.getAsDeclaration()) {
    llvm::outs() << "DECL FRAGMENT\n";
    D->dump();
  } else if (Type *T = C.getAsType()) {
    llvm::outs() << "TYPE FRAGMENT\n";
    D->dump();
  } else {
    Diag(Reflection->getExprLoc(), diag::err_not_a_reflection);
    return DeclGroupPtrTy();
  }
  
  return DeclGroupPtrTy();
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
class SourceCodeInjector : public TreeTransform<SourceCodeInjector> {
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

public:
  SourceCodeInjector(Sema &SemaRef, DeclContext *DC)
      : TreeTransform<SourceCodeInjector>(SemaRef), SourceDC(DC), 
        ReplacePlaceholders(false) {
    assert(!isa<CXXFragmentDecl>(DC) && "Source context cannot be a fragment");        
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
      PlaceholderValues[Placeholder] = TV;

      ++PlaceIter;
      ++FieldIter;
    }

    // // Build a mapping from each placeholder to its corresponding value.
    // for (std::size_t I = 0; I < Captures.size(); ++I) {
    //   assert(Iter != End && "ran out of declarations");
    //   const Expr *Capture = S->getCapture(I);
    //   ++Iter;
    // }

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
    if (Known != TransformedLocalDecls.end()) {
      return Known->second;
    }

    // Don't transform declarations that are not local to the source context.
    //
    // FIXME: Is there a better way to determine whether a declaration belongs
    // to a fragment?
    DeclContext *DC = D->getDeclContext();
    while (DC && DC != SourceDC)
      DC = DC->getParent();
    if (DC)
      return TransformLocalDecl(Loc, D);
    else
      return D;
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


/// Returns the transformed statement S. 
bool Sema::InjectBlockStatements(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isFunctionOrMethod())
    return InvalidInjection(*this, POI, 0, CurContext);

  // Note that we are instantiating a template.
  InstantiatingTemplate Inst(*this, POI);

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
  InstantiatingTemplate Inst(*this, POI);

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

bool Sema::InjectReflectedDeclaration(SourceLocation POI, InjectionInfo &II) {
#if 0
  // Note that we are instantiating a template.
  InstantiatingTemplate Inst(*this, POI);
  
  const CXXInjectionStmt *IS = cast<CXXInjectionStmt>(II.Injection);
  Decl *D = IS->getReflectedDeclaration();

  // Determine if we can actually apply the injection. In general, the contexts
  // of the injected declaration and the current context must be the same.
  //
  // FIXME: This is probably overly protective; it isn't entirely unreasonable
  // to think about injecting namespace members as static members of a class.
  DeclContext *SourceDC = D->getDeclContext();
  if (CurContext->isRecord() && !SourceDC->isRecord())
    return InvalidInjection(*this, POI, 1, CurContext);
  if (CurContext->isFileContext() && !SourceDC->isFileContext())
    return InvalidInjection(*this, POI, 2, CurContext);

  Decl *Source = Decl::castFromDeclContext(SourceDC);
  Decl *Target = Decl::castFromDeclContext(CurContext);
  SourceCodeInjector Injector(*this, SourceDC);
  Injector.AddSubstitution(Source, Target);

  // FIXME: Unify this with other reflection facilities.

  enum StorageKind { NoStorage, Static, Automatic, ThreadLocal };
  enum AccessKind { NoAccess, Public, Private, Protected, Default };

  StorageKind Storage = {};
  AccessKind Access = {};
  bool Constexpr = false;
  bool Virtual = false;
  bool Pure = false;

  APValue Mods = II.Modifications;
  if (!Mods.isUninit()) {
    // linkage_kind new_linkage : 2;
    // access_kind new_access : 2;
    // storage_kind new_storage : 2;
    // bool make_constexpr : 1;
    // bool make_virtual : 1;
    // bool make_pure : 1;

    Access = (AccessKind)Mods.getStructField(1).getInt().getExtValue();
    Storage = (StorageKind)Mods.getStructField(2).getInt().getExtValue();
    Constexpr = Mods.getStructField(3).getInt().getExtValue();
    Virtual = Mods.getStructField(4).getInt().getExtValue();
    Pure = Mods.getStructField(5).getInt().getExtValue();
  }

  assert(Storage != Automatic && "Can't make declarations automatic");
  assert(Storage != ThreadLocal && "Thread local storage not implemented");

  // Build the declaration.
  Decl* Result;
  if (isa<FieldDecl>(D) && (Storage == Static)) {
    llvm_unreachable("Rebuild field as var");
  } else {
    // An unmodified declaration.
    Result = Injector.TransformLocalDecl(D);
    if (!Result) {
      Target->setInvalidDecl(true);
      return false;
    }
  }

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
#endif
  return true;
}

static bool
ApplyInjection(Sema &SemaRef, SourceLocation POI, Sema::InjectionInfo &II) {
  // Get the declaration to be injected. 
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

  // Dig values of captured values for instantiation.
  CXXRecordDecl *Class = II.ReflectionType->getAsCXXRecordDecl();
  if (Class->isFragment()) {
    assert(isa<CXXRecordDecl>(Injection) || isa<NamespaceDecl>(Injection));
    DeclContext *InjectionDC = Decl::castToDeclContext(Injection);

    // The kind of fragment must (broadly) match the kind of context.
    DeclContext *CurrentDC = SemaRef.CurContext;
    if (isa<CXXRecordDecl>(Injection) && !CurrentDC->isRecord()) {
      InvalidInjection(SemaRef, POI, 1, CurrentDC);
      return false;
    } else if (isa<NamespaceDecl>(Injection) && !CurrentDC->isFileContext()) {
      InvalidInjection(SemaRef, POI, 0, CurrentDC);
      return false;
    }
    Decl *Injectee = Decl::castFromDeclContext(CurrentDC);

    // Extract the captured values for replacement.
    unsigned NumCaptures = II.ReflectionValue.getStructNumFields();
    ArrayRef<APValue> Captures(None);
    if (NumCaptures) {
      APValue *First = &II.ReflectionValue.getStructField(0);
      Captures = ArrayRef<APValue>(First, NumCaptures);
    }

    // Inject the members of the fragment.
    //
    // FIXME: Do modification traits apply to fragments? Probably not?
    SourceCodeInjector Injector(SemaRef, InjectionDC);
    Injector.AddSubstitution(Injection, Injectee);
    Injector.AddReplacements(Injection->getDeclContext(), Class, Captures);

    for (Decl *D : InjectionDC->decls()) {
      Decl *R = Injector.TransformLocalDecl(D);
      if (!R)
        Injectee->setInvalidDecl(true);
      
      if (isa<NamespaceDecl>(Injection))
        SemaRef.Consumer.HandleTopLevelDecl(DeclGroupRef(R));
    }
  } else {
    // Inject the fragment itself.

    // FIXME: Unpack and apply the modification traits.
  }

  return true;
}

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplySourceCodeModifications(SourceLocation POI, 
                                   SmallVectorImpl<InjectionInfo> &Injections) {
  bool Ok = true;
  for (InjectionInfo &II : Injections) {
    Ok &= ApplyInjection(*this, POI, II);
  }
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
  SourceCodeInjector Injector(*this, Def);

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
}
