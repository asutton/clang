//===--- SemaInject.cpp - Semantic Analysis for Reflection ----------------===//
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

DeclResult
Sema::ActOnInjectionCapture(IdentifierLocPair P) {
  IdentifierInfo *Id = P.first;
  SourceLocation IdLoc = P.second;

  // C++11 [expr.prim.lambda]p10:
  //   The identifiers in a capture-list are looked up using the usual
  //   rules for unqualified name lookup (3.4.1)
  //
  // That applies here too.
  //
  // FIXME: Generate the right diagnostics. Also, I'm not sure if this is
  // the right behavior for ambiguous names.
  DeclarationNameInfo Name(Id, IdLoc);
  LookupResult R(*this, Name, Sema::LookupOrdinaryName);
  LookupName(R, getCurScope());
  if (R.empty()) {
    Diag(IdLoc, diag::err_compiler_error) << "no such declaration to capture";
    return DeclResult(true);
  }
  else if (R.isAmbiguous()) {
    Diag(IdLoc, diag::err_compiler_error) << "ambiguous capture";
    return DeclResult(true);
  }

  // FIXME: What happens if we capture a non-variable? Can we capture a
  // using-declaration?
  Decl *D = R.getAsSingle<Decl>();
  if (!isa<VarDecl>(D)) {
    Diag(IdLoc, diag::err_compiler_error) << "capture is not a variable";
    return DeclResult(true);
  }

  VarDecl *VD = cast<VarDecl>(D);
  if (VD->getType()->isReferenceType()) {
    Diag(IdLoc, diag::err_compiler_error) << "cannot capture a reference";
    return DeclResult(true);
  }

  return D;
}

static bool ProcessCapture(Sema &SemaRef, DeclContext *DC, Expr *E)
{
  ValueDecl *D = cast<DeclRefExpr>(E)->getDecl();

  // Create a placeholder the name 'x' and dependent type. This is used to
  // dependently parse the body of the fragment. Also make a fake initializer.
  SourceLocation IdLoc = D->getLocation();
  IdentifierInfo *Id = D->getIdentifier();
  QualType T = SemaRef.Context.DependentTy;
  TypeSourceInfo *TSI = SemaRef.Context.getTrivialTypeSourceInfo(T);
  VarDecl *Placeholder = VarDecl::Create(SemaRef.Context, DC, IdLoc, IdLoc, 
                                         Id, T, TSI, SC_Static);
  Placeholder->setAccess(DC->isRecord() ? AS_private : AS_none);
  Placeholder->setConstexpr(true);
  Placeholder->setInitStyle(VarDecl::CInit);
  Placeholder->setInit(
      new (SemaRef.Context) OpaqueValueExpr(IdLoc, T, VK_RValue));
  Placeholder->setReferenced(true);
  Placeholder->markUsed(SemaRef.Context);

  DC->addDecl(Placeholder);
  return true;
}

static bool ProcessCaptures(Sema &SemaRef, DeclContext *DC, 
                            CXXInjectionStmt::capture_range Captures) {
  return std::all_of(Captures.begin(), Captures.end(), [&](Expr *E) {
    return ProcessCapture(SemaRef, DC, E);
  });
}

/// Returns a partially constructed injection statement.
StmtResult Sema::ActOnInjectionStmt(Scope *S, SourceLocation ArrowLoc,
                                    unsigned IK, CapturedDeclsList &Captures) {
  // We're not actually capture declarations, we're capturing an expression
  // that computes the value of the capture declaration. Build an expression
  // that reads each value and converts to an rvalue.
  //
  // FIXME: The source location for references is way off. We need to forward 
  // a vector of decl/location pairs.
  SmallVector<Expr *, 4> Refs(Captures.size());
  std::transform(Captures.begin(), Captures.end(), Refs.begin(), 
    [&](Decl *D) -> Expr * {
    ValueDecl *VD = cast<ValueDecl>(D);
    QualType T = VD->getType();

    // FIXME: Ultimately, we want an rvalue containing whatever aggregate
    // has been referenced. However, there are no standard conversions for
    // class types; we would actually be initializing a new temporary, which
    // is not at all what we want.
    return new (Context) DeclRefExpr(VD, false, T, VK_LValue, ArrowLoc);
  });

  CXXInjectionStmt *Injection =
      new (Context) CXXInjectionStmt(Context, ArrowLoc, Refs);

  // Pre-build the declaration for lambda stuff.
  if (IK == IK_Block) {
    LambdaScopeInfo *LSI = PushLambdaScope();

    // Build the expression
    //
    //    []() -> auto compound-statement
    //
    // where compound-statement is the as-of-yet parsed body of the injection.
    bool KnownDependent = false;
    if (S && S->getTemplateParamParent())
      KnownDependent = true;

    FunctionProtoType::ExtProtoInfo EPI(
        Context.getDefaultCallingConvention(/*IsVariadic=*/false,
                                            /*IsCXXMethod=*/true));
    EPI.TypeQuals |= DeclSpec::TQ_const;
    QualType MethodTy = 
        Context.getFunctionType(Context.getAutoDeductType(), None, EPI);
    TypeSourceInfo *MethodTyInfo = Context.getTrivialTypeSourceInfo(MethodTy);

    LambdaIntroducer Intro;
    Intro.Range = SourceRange(ArrowLoc);
    Intro.Default = LCD_None;

    CXXRecordDecl *Closure = createLambdaClosureType(
        Intro.Range, MethodTyInfo, KnownDependent, Intro.Default);

    // Inject captured variables here.
    ProcessCaptures(*this, Closure, Injection->captures());

    CXXMethodDecl *Method =
        startLambdaDefinition(Closure, Intro.Range, MethodTyInfo, ArrowLoc,
                              None, /*IsConstexprSpecified=*/false);
    Method->setFragment(true);

    buildLambdaScope(LSI, Method, Intro.Range, Intro.Default, Intro.DefaultLoc,
                     /*ExplicitParams=*/false,
                     /*ExplicitResultType=*/true,
                     /*Mutable=*/false);

    // Set the method on the declaration.
    Injection->setBlockInjection(Method);
  }

  return Injection;
}

void Sema::ActOnStartBlockFragment(Scope *S) {
  LambdaScopeInfo *LSI = cast<LambdaScopeInfo>(FunctionScopes.back());
  PushDeclContext(S, LSI->CallOperator);
  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);
}

void Sema::ActOnFinishBlockFragment(Scope *S, Stmt *Body) {
  ActOnLambdaExpr(Body->getLocStart(), Body, S);
}

/// Associate the fragment with the injection statement and process any 
/// captured declarations.
void Sema::ActOnStartClassFragment(Stmt *S, Decl *D) {
  CXXInjectionStmt *Injection = cast<CXXInjectionStmt>(S);
  CXXRecordDecl *Class = cast<CXXRecordDecl>(D);
  Class->setFragment(true);
  Injection->setClassInjection(Class);
  ProcessCaptures(*this, Class, Injection->captures());
}

/// Returns the completed injection statement.
///
/// FIXME: Is there any final processing we need to do?
void Sema::ActOnFinishClassFragment(Stmt *S) { }

/// Called prior to the parsing of namespace members. This injects captured
/// declarations for the purpose of lookup. Returns false if this fails.
void Sema::ActOnStartNamespaceFragment(Stmt *S, Decl *D) {
  CXXInjectionStmt *Injection = cast<CXXInjectionStmt>(S);
  NamespaceDecl *Ns = cast<NamespaceDecl>(D);
  Ns->setFragment(true);
  Injection->setNamespaceInjection(Ns);
  ProcessCaptures(*this, Ns, Injection->captures());
}

/// Returns the completed injection statement.
///
/// FIXME: Is there any final processing to do?
void Sema::ActOnFinishNamespaceFragment(Stmt *S) { }

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

  // The declaration context containing the code to be injected. This is either
  // a function (for block injection), a class (for class injection), or a
  // namespace (for namespace injection).
  DeclContext *SrcContext;

public:
  SourceCodeInjector(Sema &SemaRef, DeclContext *DC)
      : TreeTransform<SourceCodeInjector>(SemaRef), SrcContext(DC) {}

  // Always rebuild nodes; we're effectively copying from one AST to another.
  bool AlwaysRebuild() const { return true; }

  // Replace the declaration From (in the injected statement or members) with
  // the declaration To (derived from the target context).
  void AddSubstitution(Decl *From, Decl *To) {
    transformedLocalDecl(From, To);
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

  Decl *TransformDecl(SourceLocation Loc, Decl *D) {
    if (!D)
      return nullptr;

    // Search for a previous transformation. We need to do this before the
    // context search below.
    auto Known = TransformedLocalDecls.find(D);
    if (Known != TransformedLocalDecls.end())
      return Known->second;

    // Don't transform declarations that are not local to the source context.
    //
    // FIXME: Is there a better way to determine nesting?
    DeclContext *DC = D->getDeclContext();
    while (DC && DC != SrcContext)
      DC = DC->getParent();
    if (!DC)
      return D;

    return TransformLocalDecl(Loc, D);
  }
};


/// Returns the transformed statement S. 
bool Sema::InjectBlockStatements(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isFunctionOrMethod())
    return InvalidInjection(*this, POI, 0, CurContext);

  /*
  SourceCodeInjector Injector(*this, S->getInjectionContext());

  // Transform each statement in turn. Note that we build build a compound
  // statement from all injected statements at the point of injection.
  CompoundStmt *Block = S->getInjectedBlock();
  for (Stmt *B : Block->body()) {
    StmtResult R = Injector.TransformStmt(B);
    if (R.isInvalid())
      return false;
    InjectedStmts.push_back(R.get());
  }
  */
  
  return true;
}

bool Sema::InjectClassMembers(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isRecord())
    return InvalidInjection(*this, POI, 1, CurContext);

  const CXXInjectionStmt *IS = cast<CXXInjectionStmt>(II.Injection);

  CXXRecordDecl *Target = cast<CXXRecordDecl>(CurContext);
  CXXRecordDecl *Source = IS->getInjectedClass();
  SourceCodeInjector Injector(*this, Source);
  Injector.AddSubstitution(Source, Target);

  auto DeclIter = Source->decls_begin();
  auto DeclEnd = Source->decls_end();
  const SmallVectorImpl<APValue> &Values = II.CaptureValues;
  for (std::size_t I = 0; I < IS->getNumCaptures(); ++I) {
    assert(DeclIter != DeclEnd && "ran out of declarations");

    // Unpack information about 
    Expr *E = const_cast<Expr *>(IS->getCapture(I));
    QualType T = E->getType();
    TypeSourceInfo *TSI = Context.getTrivialTypeSourceInfo(T);

    // Build a new placeholder for the destination context.
    VarDecl *Placeholder = cast<VarDecl>(*DeclIter);
    SourceLocation Loc = Placeholder->getLocation();
    IdentifierInfo *Id = Placeholder->getIdentifier();
    VarDecl *Replacement = 
        VarDecl::Create(Context, Target, Loc, Loc, Id, T, TSI, SC_Static);
    Replacement->setAccess(AS_private);
    Replacement->setConstexpr(true);
    Replacement->setInitStyle(VarDecl::CInit);
    Replacement->setInit(new (Context) CXXConstantExpr(E, Values[I]));    
    Replacement->setReferenced(true);
    Replacement->markUsed(Context);

    // Substitute the placeholder for its replacement.
    Injector.AddSubstitution(Placeholder, Replacement);
      
    ++DeclIter;
  }

  while (DeclIter != DeclEnd) {
    Decl *Member = *DeclIter;
    if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(Member)) {
      // The top-level injected class name is not injected.
      if (RD->isInjectedClassName())
        continue;
    }

    if (!Injector.TransformLocalDecl(Member))
      Target->setInvalidDecl(true);

    ++DeclIter;
  }

  return !Target->isInvalidDecl();
}

bool Sema::InjectNamespaceMembers(SourceLocation POI, InjectionInfo &II) {
  if (!CurContext->isFileContext())
    return InvalidInjection(*this, POI, 2, CurContext);

  /*
  NamespaceDecl *Source = D->getInjectedNamespace();
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

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplySourceCodeModifications(SourceLocation POI, 
                                   SmallVectorImpl<InjectionInfo> &Injections) {
  for (InjectionInfo &II : Injections) {
    // Unpack the injection to see how it should be applied.
    const Stmt *S = II.Injection;
    if (const auto *IS = dyn_cast<CXXInjectionStmt>(S)) {
      if (IS->isBlockInjection())
        InjectBlockStatements(POI, II);
      else if (IS->isClassInjection())
        InjectClassMembers(POI, II);
      else if (IS->isNamespaceInjection())
        InjectNamespaceMembers(POI, II);
      else
        llvm_unreachable("Unknown injection context");
    } else if (const auto *RTE = dyn_cast<ReflectionTraitExpr>(S)) {
      auto *E = const_cast<ReflectionTraitExpr *>(RTE);
      if (RTE->getTrait() == BRT_ModifyAccess)
        ModifyDeclarationAccess(E);
      else if (RTE->getTrait() == BRT_ModifyVirtual)
        ModifyDeclarationVirtual(E);
      else if (RTE->getTrait() == URT_ModifyConstexpr)
        ModifyDeclarationConstexpr(E);
      else
        llvm_unreachable("Unknown reflection trait");
    } else
      llvm_unreachable("Invalid injection");
  }
  return true;
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
                          CXXRecordDecl *Proto,
                          CXXRecordDecl *Final,
                          SmallVectorImpl<Decl *> &Fields) {
  CXXRecordDecl *Def = Meta->getDefinition();

  // Build a new class to use as an intermediary for containing transformed
  // declarations. We'll perform a second set of substitutions to move the
  // content into the final class.
  CXXRecordDecl *Scratch = CXXRecordDecl::Create(Context, Proto->getTagKind(),
                                                 CurContext, 
                                                 Proto->getLocStart(), 
                                                 Proto->getLocation(),
                                                 Proto->getIdentifier(),
                                                 /*PrevDecl=*/nullptr);
  Scratch->setFragment(true);
  Scratch->startDefinition();
  // llvm::outs() << "--- FIRST PASS ---\n";
  // Def->dump();
  // Proto->dump();
  {
    ContextRAII SavedContext(*this, Scratch);
    SourceCodeInjector Injector(*this, Def);
    Injector.AddSubstitution(Def, Proto);

    for (Decl *D : Def->decls()) {
      if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(D)) {
        if (RD->isInjectedClassName())
          // Skip the injected class name.
          continue;
      }

      if (!Injector.TransformDecl(D))
        Final->setInvalidDecl(true);
    }
  }
  Scratch->completeDefinition();

  if (Final->isInvalidDecl())
    return;

  // llvm::outs() << "*** SECOND PASS ***\n";
  // Scratch->dump();
  // Scratch->print(llvm::outs());
  // llvm::outs() << '\n';

  // Perform a second transformation that injects the scratch injections into
  // the final class.
  {
    ContextRAII SavedContext(*this, Final);
    SourceCodeInjector Injector(*this, Scratch);
    Injector.AddSubstitution(Scratch, Final);
    Injector.AddSubstitution(Proto, Final);

    for (Decl *D : Scratch->decls()) {
      Decl *R = Injector.TransformDecl(D);
      if (!R) {
        Final->setInvalidDecl(true);
        return;
      }
      if (isa<FieldDecl>(R))
        Fields.push_back(R);
    }
  }

  // llvm::outs() << "*** FINAL CLASS ***\n";
  // Final->dump();
  // Final->print(llvm::outs());
}
