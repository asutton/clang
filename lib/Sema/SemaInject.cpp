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

/// Returns a partially constructed block injection.
StmtResult Sema::ActOnBlockInjection(Scope *S, SourceLocation ArrowLoc) {
  LambdaScopeInfo *LSI = PushLambdaScope();

  // Build the expression
  //
  //    []() -> auto compound-statement
  //
  // where compound-statement is the as-of-yet parsed body of the injection.
  const bool KnownDependent = S->getTemplateParamParent();

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
  CXXMethodDecl *Method =
      startLambdaDefinition(Closure, Intro.Range, MethodTyInfo, ArrowLoc,
                            None, /*IsConstexprSpecified=*/false);
  buildLambdaScope(LSI, Method, Intro.Range, Intro.Default, Intro.DefaultLoc,
                   /*ExplicitParams=*/false,
                   /*ExplicitResultType=*/true,
                   /*Mutable=*/false);

  return new (Context) CXXInjectionStmt(ArrowLoc, IK_Block, Method);
}

void Sema::ActOnStartBlockInjectionBody(Scope *S) {
  LambdaScopeInfo *LSI = cast<LambdaScopeInfo>(FunctionScopes.back());
  PushDeclContext(S, LSI->CallOperator);
  PushExpressionEvaluationContext(
      ExpressionEvaluationContext::PotentiallyEvaluated);
}

void Sema::ActOnFinishBlockInjectionBody(Scope *S, Stmt *Body) {
  ActOnLambdaExpr(Body->getLocStart(), Body, S);
}


StmtResult Sema::ActOnCXXClassInjection(SourceLocation ArrowLoc, Decl *D) {
  /// FIXME: Is there any checking that we need to apply to the members of
  /// this class?
  return new (Context) CXXInjectionStmt(ArrowLoc, IK_Class, D);
}

StmtResult Sema::ActOnCXXNamespaceInjection(SourceLocation ArrowLoc, Decl *D) {
  /// FIXME: Is there any checking that we need to apply to the members of
  /// this namespace?
  return new (Context) CXXInjectionStmt(ArrowLoc, IK_Namespace, D);
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

  Decl *TransformDecl(Decl *D);
  Decl *TransformDecl(SourceLocation, Decl *D);
  Decl *TransformDeclImpl(SourceLocation, Decl *D);
  Decl *TransformVarDecl(VarDecl *D);
  Decl *TransformParmVarDecl(ParmVarDecl *D);
  Decl *TransformFunctionDecl(FunctionDecl *D);
  Decl *TransformCXXRecordDecl(CXXRecordDecl *D);
  Decl *TransformCXXMethodDecl(CXXMethodDecl *D);
  Decl *TransformCXXConstructorDecl(CXXConstructorDecl *D);
  Decl *TransformCXXDestructorDecl(CXXDestructorDecl *D);
  Decl *TransformFieldDecl(FieldDecl *D);
  Decl *TransformConstexprDecl(ConstexprDecl *D);

  void TransformFunctionParameters(FunctionDecl *D, FunctionDecl *R);
  void TransformFunctionDefinition(FunctionDecl *D, FunctionDecl *R);
  void TransformAttributes(Decl *D, Decl *R);
};

Decl *SourceCodeInjector::TransformDecl(Decl *D) {
  return TransformDecl(D->getLocation(), D);
}

Decl *SourceCodeInjector::TransformDecl(SourceLocation Loc, Decl *D) {
  if (!D)
    return nullptr;

  // Don't transform declarations that are not local to the source context.
  //
  // FIXME: Is there a better way to determine nesting?
  DeclContext *DC = D->getDeclContext();
  while (DC && DC != SrcContext)
    DC = DC->getParent();
  if (!DC)
    return D;

  // Search for a previous transformation.
  auto Known = TransformedLocalDecls.find(D);
  if (Known != TransformedLocalDecls.end())
    return Known->second;

  Decl *R = TransformDeclImpl(Loc, D);
  TransformAttributes(D, R);
  return R;
}

Decl *SourceCodeInjector::TransformDeclImpl(SourceLocation Loc, Decl *D) {
  switch (D->getKind()) {
  default:
    break;
  case Decl::Var:
    return TransformVarDecl(cast<VarDecl>(D));
  case Decl::ParmVar:
    return TransformParmVarDecl(cast<ParmVarDecl>(D));
  case Decl::Function:
    return TransformFunctionDecl(cast<FunctionDecl>(D));
  case Decl::CXXRecord:
    return TransformCXXRecordDecl(cast<CXXRecordDecl>(D));
  case Decl::CXXMethod:
    return TransformCXXMethodDecl(cast<CXXMethodDecl>(D));
  case Decl::CXXConstructor:
    return TransformCXXConstructorDecl(cast<CXXConstructorDecl>(D));
  case Decl::CXXDestructor:
    return TransformCXXDestructorDecl(cast<CXXDestructorDecl>(D));
  case Decl::Field:
    return TransformFieldDecl(cast<FieldDecl>(D));
  case Decl::Constexpr:
    return TransformConstexprDecl(cast<ConstexprDecl>(D));
  }
  llvm_unreachable("Injecting unknown declaration");
}

Decl *SourceCodeInjector::TransformVarDecl(VarDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  VarDecl *R = VarDecl::Create(SemaRef.Context, 
                               SemaRef.CurContext, 
                               D->getLocation(), 
                               D->getLocation(),
                               D->getIdentifier(), 
                               TypeInfo->getType(), 
                               TypeInfo, 
                               D->getStorageClass());
  transformedLocalDecl(D, R);

  // FIXME: Transform attributes.

  SemaRef.CurContext->addDecl(R);

  // Transform the initializer and associated properties of the definition.
  if (D->getInit()) {
    // Propagate the inline flag.
    if (D->isInlineSpecified())
      R->setInlineSpecified();
    else if (D->isInline())
      R->setImplicitlyInline();

    if (D->getInit()) {
      if (R->isStaticDataMember() && !D->isOutOfLine())
        SemaRef.PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::ConstantEvaluated, D);
      else
        SemaRef.PushExpressionEvaluationContext(
          Sema::ExpressionEvaluationContext::PotentiallyEvaluated, D);

      ExprResult Init;
      {
        Sema::ContextRAII SwitchContext(SemaRef, R->getDeclContext());
        Init = TransformInitializer(D->getInit(),
                                    D->getInitStyle() == VarDecl::CallInit);
      }
      if (!Init.isInvalid()) {
        if (Init.get())
          SemaRef.AddInitializerToDecl(R, Init.get(), D->isDirectInit());
        else
          SemaRef.ActOnUninitializedDecl(R);
      } else
        R->setInvalidDecl();
    }
  }

  return R;
}


Decl *SourceCodeInjector::TransformParmVarDecl(ParmVarDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  auto *R = SemaRef.CheckParameter(SemaRef.Context.getTranslationUnitDecl(),
                                   D->getLocation(), D->getLocation(),
                                   D->getIdentifier(), TypeInfo->getType(),
                                   TypeInfo, D->getStorageClass());
  transformedLocalDecl(D, R);

  // FIXME: Are there any attributes we need to set?
  // FIXME: Transform the default argument also.

  return R;
}

Decl *SourceCodeInjector::TransformFunctionDecl(FunctionDecl *D) {
  DeclarationNameInfo NameInfo = TransformDeclarationNameInfo(D->getNameInfo());
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  FunctionDecl *R = FunctionDecl::Create(
      SemaRef.Context, SemaRef.CurContext, D->getLocation(), NameInfo.getLoc(),
      NameInfo.getName(), TypeInfo->getType(), TypeInfo, D->getStorageClass(),
      D->isInlineSpecified(), D->hasWrittenPrototype(), D->isConstexpr());
  transformedLocalDecl(D, R);

  TransformFunctionParameters(D, R);

  // Copy other properties.
  R->setAccess(D->getAccess()); // FIXME: Is this right?
  if (D->isDeletedAsWritten())
    SemaRef.SetDeclDeleted(R, R->getLocation());

  // FIXME: Make sure that we aren't overriding an existing declaration.
  SemaRef.CurContext->addDecl(R);

  TransformFunctionDefinition(D, R);
  return R;
}

Decl *SourceCodeInjector::TransformFieldDecl(FieldDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  FieldDecl *R = FieldDecl::Create(
      SemaRef.Context, SemaRef.CurContext, D->getLocation(), D->getLocation(),
      D->getIdentifier(), TypeInfo->getType(), TypeInfo,
      /*Bitwidth*/ nullptr, D->isMutable(), D->getInClassInitStyle());

  transformedLocalDecl(D, R);

  // FIXME: What other properties do we need to copy?
  R->setAccess(D->getAccess());

  SemaRef.CurContext->addDecl(R);

  // FIXME: Transform the initializer, if present.
  return R;
}

Decl *SourceCodeInjector::TransformCXXRecordDecl(CXXRecordDecl *D) {
  DeclarationNameInfo DN(D->getDeclName(), D->getLocation());
  DeclarationNameInfo DNI = TransformDeclarationNameInfo(DN);

  // FIXME: If D has a previous declaration, then we need to find the
  // previous declaration of R.

  CXXRecordDecl *R = CXXRecordDecl::Create(SemaRef.Context, D->getTagKind(),
                                           SemaRef.CurContext, D->getLocStart(), 
                                           D->getLocation(),
                                           DNI.getName().getAsIdentifierInfo(),
                                           /*PrevDecl=*/nullptr);
  transformedLocalDecl(D, R);

  // FIXME: Propagate attributes of the class.

  SemaRef.CurContext->addDecl(R);

  if (D->hasDefinition()) {
    R->startDefinition();

    // FIXME: Transform base class specifiers.

    // Recursively transform declarations.
    Sema::ContextRAII SwitchContext(SemaRef, R);
    for (Decl *Member : D->decls()) {
      // Don't transform invalid declarations.
      if (Member->isInvalidDecl())
        continue;

      // Don't transform non-members appearing in a class.
      if (Member->getDeclContext() != D)
        continue;
      
      TransformDecl(Member);
    }

    R->completeDefinition();
  }
 
  return R;
}

Decl *SourceCodeInjector::TransformCXXMethodDecl(CXXMethodDecl *D) {
  DeclarationNameInfo NameInfo = TransformDeclarationNameInfo(D->getNameInfo());

  // FIXME: The exception specification is not being translated correctly
  // for destructors (probably others).
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());

  // FIXME: Handle conversion operators.
  CXXRecordDecl *CurClass = cast<CXXRecordDecl>(SemaRef.CurContext);
  CXXMethodDecl *R;
  if (auto *Ctor = dyn_cast<CXXConstructorDecl>(D))
    R = CXXConstructorDecl::Create(SemaRef.Context, CurClass, D->getLocation(),
                                   NameInfo, TypeInfo->getType(), TypeInfo,
                                   Ctor->isExplicitSpecified(),
                                   Ctor->isInlineSpecified(),
                                   /*isImplicitlyDeclared=*/false,
                                   Ctor->isConstexpr(), InheritedConstructor());
  else if (isa<CXXDestructorDecl>(D))
    R = CXXDestructorDecl::Create(SemaRef.Context, CurClass, D->getLocation(),
                                  NameInfo, TypeInfo->getType(), TypeInfo,
                                  D->isInlineSpecified(),
                                  /*isImplicitlyDeclared=*/false);
  else
    R = CXXMethodDecl::Create(SemaRef.Context, CurClass, D->getLocStart(),
                              NameInfo, TypeInfo->getType(), TypeInfo,
                              D->getStorageClass(), D->isInlineSpecified(),
                              D->isConstexpr(), D->getLocEnd());
  transformedLocalDecl(D, R);

  TransformFunctionParameters(D, R);

  // FIXME: What other properties do I need to set?
  R->setAccess(D->getAccess());
  if (D->isExplicitlyDefaulted())
    SemaRef.SetDeclDefaulted(R, R->getLocation());
  if (D->isDeletedAsWritten())
    SemaRef.SetDeclDeleted(R, R->getLocation());
  if (D->isVirtualAsWritten())
    R->setVirtualAsWritten(true);
  if (D->isPure())
    SemaRef.CheckPureMethod(R, SourceRange());

  // FIXME: Make sure that we aren't overriding an existing declaration.
  SemaRef.CurContext->addDecl(R);

  TransformFunctionDefinition(D, R);
  return R;
}

Decl *SourceCodeInjector::TransformCXXConstructorDecl(CXXConstructorDecl *D) {
  return TransformCXXMethodDecl(D);
}

Decl *SourceCodeInjector::TransformCXXDestructorDecl(CXXDestructorDecl *D) {
  return TransformCXXMethodDecl(D);
}

/// Transform each parameter of a function.
void SourceCodeInjector::TransformFunctionParameters(FunctionDecl *D,
                                                     FunctionDecl *R) {
  llvm::SmallVector<ParmVarDecl *, 4> Params;
  for (auto I = D->param_begin(), E = D->param_end(); I != E; ++I) {
    ParmVarDecl *P = cast<ParmVarDecl>(TransformDecl(*I));
    P->setOwningFunction(R);
    Params.push_back(P);
  }
  R->setParams(Params);
}

/// Transform the body of a function.
void SourceCodeInjector::TransformFunctionDefinition(FunctionDecl *D,
                                                     FunctionDecl *R) {
  // Transform the method definition.
  if (Stmt *S = D->getBody()) {
    // Set up the semantic context needed to translate the function. We don't
    // use PushDeclContext() because we don't have a scope.
    EnterExpressionEvaluationContext EvalContext(SemaRef,
                       Sema::ExpressionEvaluationContext::PotentiallyEvaluated);
    SemaRef.ActOnStartOfFunctionDef(nullptr, R);
    Sema::ContextRAII SavedContext(SemaRef, R);
    StmtResult Body = TransformStmt(S);
    if (Body.isInvalid()) {
      // FIXME: Diagnose a transformation error?
      R->setInvalidDecl();
      return;
    }
    SemaRef.ActOnFinishFunctionBody(R, Body.get());
  }
}

void SourceCodeInjector::TransformAttributes(Decl *D, Decl *R) {
  // FIXME: The general rule for TreeTransform<>::TransformAttr is to simply
  // return the original attribute. We may actually need to perform 
  // substitutions in derived kinds of attributes.
  for (Attr *Old : D->attrs()) {
    const Attr *New = TransformAttr(Old);
    if (New == Old)
      R->addAttr(Old->clone(SemaRef.Context));
    else
      R->addAttr(const_cast<Attr *>(New));
  }
}

/// Returns the transformed statement S. 
bool Sema::InjectBlockStatements(SourceLocation POI, CXXInjectionStmt *S) {
  if (!CurContext->isFunctionOrMethod())
    return InvalidInjection(*this, POI, 0, CurContext);

  // FIXME: At some point, we'll have parameters to bind.
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
  
  return true;
}

bool Sema::InjectClassMembers(SourceLocation POI, CXXInjectionStmt *S) {
  if (!CurContext->isRecord())
    return InvalidInjection(*this, POI, 1, CurContext);

  CXXRecordDecl *Target = cast<CXXRecordDecl>(CurContext);
  CXXRecordDecl *Source = S->getInjectedClass();
  SourceCodeInjector Injector(*this, Source);
  Injector.AddSubstitution(Source, Target);

  // FIXME: What should we do with injected base classes? Actually, we don't
  // parse those, so there's not much we can do.

  // Transform each declaration in turn.
  for (Decl *Member : Source->decls()) {
    if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(Member)) {
      // The top-level injected class name is not injected.
      if (RD->isInjectedClassName())
        continue;
    }
    Injector.TransformDecl(Member);
  }

  return true;
}

bool Sema::InjectNamespaceMembers(SourceLocation POI, CXXInjectionStmt *D) {
  if (!CurContext->isFileContext())
    return InvalidInjection(*this, POI, 2, CurContext);

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

  return true;
}

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. The point of injection (POI) is the point at
/// which the injection is applied.
///
/// \returns  true if no errors are encountered, false otherwise.
bool Sema::ApplySourceCodeModifications(SourceLocation POI, 
                                        SmallVectorImpl<Stmt *> &Stmts) {
  for (Stmt *S : Stmts) {
    if (CXXInjectionStmt *IS = dyn_cast<CXXInjectionStmt>(S)) {
      if (IS->isBlockInjection())
        InjectBlockStatements(POI, IS);
      else if (IS->isClassInjection())
        InjectClassMembers(POI, IS);
      else if (IS->isNamespaceInjection())
        InjectNamespaceMembers(POI, IS);
      else
        llvm_unreachable("Unknown injection context");
    } else if (ReflectionTraitExpr *RTE = dyn_cast<ReflectionTraitExpr>(S)) {
      if (RTE->getTrait() == BRT_ModifyAccess)
        ModifyDeclarationAccess(RTE);
      else if (RTE->getTrait() == BRT_ModifyVirtual)
        ModifyDeclarationVirtual(RTE);
      else
        llvm_unreachable("Unknown reflection trait");
    } else
      llvm_unreachable("Invalid injection");
  }
  return true;
}

Decl *SourceCodeInjector::TransformConstexprDecl(ConstexprDecl *D) {
  // We can use the ActOn* members since the initial parsing for these
  // declarations is trivial (i.e., don't have to translate declarators).
  unsigned ScopeFlags; // Unused
  Decl *New = SemaRef.ActOnConstexprDecl(SemaRef.getCurScope(),
                                         D->getLocation(), ScopeFlags);
  SemaRef.ActOnStartConstexprDecl(SemaRef.getCurScope(), New);
  StmtResult S = TransformStmt(D->getBody());
  if (!S.isInvalid())
    SemaRef.ActOnFinishConstexprDecl(SemaRef.getCurScope(), New, S.get());
  else
    SemaRef.ActOnConstexprDeclError(SemaRef.getCurScope(), New);
  return New;
}


/// Copy, by way of transforming, the members of the given C++ metaclass into
/// the target class.
///
/// The \p Fields parameter is used to store injected fields for subsequent
/// analysis by ActOnFields().
///
/// Note that this is always called within the scope of the receiving class,
/// as if the declarations were being written in-place.
void Sema::InjectMetaclassMembers(MetaclassDecl *Meta, CXXRecordDecl *Class,
                                  SmallVectorImpl<Decl *> &Fields) {
  // llvm::errs() << "INJECT MEMBERS\n";
  // Meta->dump();

  // Make the receiving class the top-level context.
  Sema::ContextRAII SavedContext(*this, Class);

  // Inject each metaclass member in turn.
  CXXRecordDecl *Def = Meta->getDefinition();

  SourceCodeInjector Injector(*this, Meta);
  Injector.AddSubstitution(Def, Class);

  // Propagate attributes on a metaclass to the destination class.
  Injector.TransformAttributes(Def, Class);

  // Recursively inject base classes.
  for (CXXBaseSpecifier &B : Def->bases()) {
    QualType T = B.getType();
    CXXRecordDecl *BaseClass = T->getAsCXXRecordDecl();
    assert(BaseClass->isMetaclassDefinition() && 
           "Metaclass inheritance from regular class");
    MetaclassDecl *BaseMeta = cast<MetaclassDecl>(BaseClass->getDeclContext());
    InjectMetaclassMembers(BaseMeta, Class, Fields);
  }

  // Inject the members.
  for (Decl *D : Def->decls()) {
    if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(D)) {
      if (RD->isInjectedClassName())
        // Skip the injected class name.
        continue;
    }

    // Inject the declaration into the class. The injection site is the
    // closing brace of the class body.
    if (Decl *R = Injector.TransformDecl(D)) {
      if (isa<FieldDecl>(R))
        Fields.push_back(R);
    }
  }

  llvm::outs() << "HERE: " << Class->hasAttr<PackedAttr>() << '\n';

  // llvm::errs() << "RESULTING CLASS\n";
  // Class->dump();
}
