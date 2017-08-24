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
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Sema/SemaInternal.h"

using namespace clang;
using namespace sema;

// Find variables to capture in the given scope. 
static void FindCapturesInScope(Sema &SemaRef, Scope *S, 
                                SmallVectorImpl<VarDecl *> &Vars) {
  for (Decl *D : S->decls()) {
    if (VarDecl *Var = dyn_cast<VarDecl>(D))
      if (Var->isLocalVarDeclOrParm())
        Vars.push_back(Var);
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
/// automatic variables captured.
void Sema::ActOnCXXFragmentCapture(SmallVectorImpl<Expr *> &Captures) {
  assert(Captures.empty() && "Captures already specified");
  SmallVector<VarDecl *, 8> Vars;
  FindCaptures(*this, CurScope, getCurFunctionDecl(), Vars);
  ReferenceCaptures(*this, Vars, Captures);
}

/// Called at the start of a source code fragment to establish the fragment
/// declaration and placeholders. 
Decl *Sema::ActOnStartCXXFragment(SourceLocation Loc, 
                                  SmallVectorImpl<Expr *> &Captures) {
  CXXFragmentDecl *Fragment = CXXFragmentDecl::Create(Context, CurContext, Loc);
  CreatePlaceholders(*this, Fragment, Captures);
  return Fragment;
}

// Binds the content the fragment declaration. Returns the updated fragment.
Decl *Sema::ActOnFinishCXXFragment(Decl *Fragment, Decl *Content) {
  CXXFragmentDecl *FD = cast<CXXFragmentDecl>(Fragment);
  FD->setContent(Content);
  return FD;
}

/// Builds a new fragment expression.
ExprResult Sema::ActOnCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  return BuildCXXFragmentExpr(Loc, Captures, Fragment);
}

/// Builds a new fragment expression.
ExprResult Sema::BuildCXXFragmentExpr(SourceLocation Loc, 
                                      SmallVectorImpl<Expr *> &Captures, 
                                      Decl *Fragment) {
  CXXFragmentDecl *FD = cast<CXXFragmentDecl>(Fragment);
  ExprResult E = BuildDeclReflection(Loc, FD->getContent());
  if (E.isInvalid())
    return ExprError();
  QualType T = E.get()->getType();
  return new (Context) CXXFragmentExpr(Context, Loc, T, Captures, FD, E.get());
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

  // FIXME: How do we access local modifications. We could attach an
  // accessor expression like we do in the commented code below.

  return new (Context) CXXInjectionStmt(Loc, Reflection);
}

#if 0
/// Generates an injection for a copy of the reflected declaration.
StmtResult Sema::ActOnReflectionInjection(SourceLocation ArrowLoc, Expr *Ref) {
  llvm_unreachable("not implemented");
  if (Ref->isTypeDependent() || Ref->isValueDependent())
    return new (Context) CXXInjectionStmt(ArrowLoc, Ref);

  Decl *D = GetReflectedDeclaration(Ref);
  if (!D)
    return StmtError();

  // Build the expression `ref.mods` to extract the list of local modifications
  // during evaluation. Apply an lvalue to rvalue conversion so we get the
  // referenced value during evaluation.

  SourceLocation Loc = Ref->getLocStart();
  UnqualifiedId Id;
  Id.setIdentifier(PP.getIdentifierInfo("mods"), Loc);
  CXXScopeSpec SS;
  ExprResult Mods = ActOnMemberAccessExpr(getCurScope(), Ref, Loc, tok::period, 
                                          SS, SourceLocation(), Id, nullptr);
  Mods = ImplicitCastExpr::Create(Context, Ref->getType(), CK_LValueToRValue,
                                  Mods.get(), nullptr, VK_RValue);

  CXXInjectionStmt *IS = new (Context) CXXInjectionStmt(ArrowLoc, Ref, D);

  // FIXME: This is not sufficient to solve the problem. We need to evaluate
  // the expression, get the APValue and attach *those* modifications to the
  // expression -- kind of like captured references (hint: reuse captures).

  if (Mods.isUsable())
    IS->setModifications(Mods.get());

  return IS;
}
#endif

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

  // The fragment containing the code to be injected. This is either
  // a function (for block injection), a class (for class injection), or a
  // namespace (for namespace injection).
  DeclContext *Fragment;

public:
  SourceCodeInjector(Sema &SemaRef, DeclContext *DC)
      : TreeTransform<SourceCodeInjector>(SemaRef), Fragment(DC), 
        ReplacePlaceholders(false) {}

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
    while (DC && DC != Fragment)
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

#if 0
// The first NumCapture declarations in the [Iter, End) are placeholders.
// Replace those with new declarations of the form:
//
//    constexpr t n = value
//
// where t, n and value are: the type of the original capture, the name
// of the captured variable, and the computed value of that expression at
// the time the capture was evaluated.
//
// Note that the replacement variables are not added to the output class.
// They are replaced during transformation.
static void ReplacePlaceholders(Sema &SemaRef, SourceCodeInjector &Injector,
                                const CXXInjectionStmt *S, 
                                const SmallVectorImpl<APValue> &Values, 
                                DeclContext::decl_iterator &Iter, 
                                DeclContext::decl_iterator End) {
  // Build a mapping from each placeholder to its corresponding value.
  for (std::size_t I = 0; I < S->getNumCaptures(); ++I) {
    assert(Iter != End && "ran out of declarations");
    const Expr *Capture = S->getCapture(I);
    TypedValue TV { Capture->getType(), Values[I] };
    Injector.PlaceholderValues[*Iter] = TV;
    ++Iter;
  }

  // Stop seeing placeholders in subsequent transformations.
  Injector.ReplacePlaceholders = true;
}
#endif

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
ApplyInjection(Sema &SemaRef, SourceLocation POI, Sema::InjectionInfo &II, 
               const CXXInjectionStmt *IS) {
#if 0
   switch (IS->getInjectionKind()) {
    case CXXInjectionStmt::BlockFragment:
      return SemaRef.InjectBlockStatements(POI, II);
    case CXXInjectionStmt::ClassFragment:
      return SemaRef.InjectClassMembers(POI, II);
    case CXXInjectionStmt::NamespaceFragment:
      return SemaRef.InjectNamespaceMembers(POI, II);
    case CXXInjectionStmt::ReflectedDecl:
      return SemaRef.InjectReflectedDeclaration(POI, II);
  }
#endif
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
    const CXXInjectionStmt *IS = dyn_cast<CXXInjectionStmt>(II.Injection);
    Ok &= ApplyInjection(*this, POI, II, IS);
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
