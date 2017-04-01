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

#include "clang/Sema/SemaInternal.h"
#include "TreeTransform.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclVisitor.h"
#include "clang/AST/ExprCXX.h"

using namespace clang;
using namespace sema;

/// Injects declarations from a metaclass definition into another class,
/// by replacing all references to the metaclass type with that of the
/// target type.
///
/// FIXME: To improve diagnostics, we'll probably want to record the source
/// of every injection. We might actually do this using a separate lexical
/// declaration context vs. semantic context and an extra flag that determines
/// how that should be interpreted.
class MetaclassInjector : public TreeTransform<MetaclassInjector> {
  /// The class containing injected declaration.
  CXXRecordDecl *Source;

  /// The class receiving injected declarations.
  CXXRecordDecl *Dest;

public:
  MetaclassInjector(Sema& SemaRef, CXXRecordDecl *S, CXXRecordDecl *D)
    : TreeTransform<MetaclassInjector>(SemaRef), Source(S), Dest(D) {
      // Explicitly re-map the the source as the destination.
      transformedLocalDecl(Source, Dest);
    }

  // Always rebuild nodes; we're effectively copying from one AST to another.
  bool AlwaysRebuild() const { return true; }

  bool TransformTemplateArgument(const TemplateArgumentLoc &Input, 
                                 TemplateArgumentLoc &Output, bool Uneval);

  Decl *TransformDecl(Decl *D);
  Decl *TransformDecl(SourceLocation, Decl *D);
  Decl *TransformVarDecl(VarDecl *D);
  Decl *TransformParmVarDecl(ParmVarDecl *D);
  Decl *TransformFunctionDecl(FunctionDecl *D);
  Decl *TransformCXXMethodDecl(CXXMethodDecl *D);
  Decl *TransformCXXConstructorDecl(CXXConstructorDecl *D);
  Decl *TransformCXXDestructorDecl(CXXDestructorDecl *D);
  Decl *TransformFieldDecl(FieldDecl *D);
  Decl *TransformConstexprDecl(ConstexprDecl *D);

  void TransformFunctionParameters(FunctionDecl *D, FunctionDecl *R);
  void TransformFunctionDefinition(FunctionDecl *D, FunctionDecl *R);
};


// For some reason, the default does not expect integer template arguments.
// So we override that behavior here.
bool MetaclassInjector::
TransformTemplateArgument(const TemplateArgumentLoc &Input,
                          TemplateArgumentLoc &Output, bool Uneval) {
  const TemplateArgument &Arg = Input.getArgument();
  if (Arg.getKind() == TemplateArgument::Integral) {
    Output = Input;
    return false;
  }
  return TreeTransform<MetaclassInjector>::TransformTemplateArgument(Input,
                                                                     Output,
                                                                     Uneval);
}

/// Look to see if the declaration has been locally transformed. If so,
/// return that. Otherwise, explicitly rebuild the declaration.
Decl *MetaclassInjector::TransformDecl(Decl *D) {
  return TransformDecl(D->getLocation(), D);
}

/// Returns true if the given declaration is not a candidate for 
/// transformation. This is true for any declaration that is not directly
/// contained within the metaclass, either directly as a member or indirectly
/// as e.g., a local variable in a member function.
static inline bool ShouldNotTransform(Decl *D, DeclContext *Cxt) {
  DeclContext *DC = D->getDeclContext();
  while (DC) {
    if (DC == Cxt)
      break;
    DC = DC->getParent();
  }
  return DC == nullptr;
}

/// Look to see if the declaration has been locally transformed. If so,
/// return that. Otherwise, explicitly rebuild the declaration.
Decl *MetaclassInjector::TransformDecl(SourceLocation Loc, Decl *D) {
  if (ShouldNotTransform(D, Source))
    return D;

  llvm::DenseMap<Decl *, Decl *>::iterator Known
    = TransformedLocalDecls.find(D);
  if (Known != TransformedLocalDecls.end())
    return Known->second;

  /// FIXME: It might be a better idea to use a DeclVisitor here.
  switch (D->getKind()) {
    default:
      D->dump();
      llvm_unreachable("Injection not implemented");
    case Decl::Var:
      return TransformVarDecl(cast<VarDecl>(D));
    case Decl::ParmVar:
      return TransformParmVarDecl(cast<ParmVarDecl>(D));
    case Decl::Function:
      return TransformFunctionDecl(cast<FunctionDecl>(D));
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

    case Decl::CXXRecord: 
    case Decl::ClassTemplate: {
      // FIXME: What other 
      // If the class is not enclosed by the metaclass, then we shouldn't
      // modify it.
      CXXRecordDecl *Class = cast<CXXRecordDecl>(D);
      if (!Source->Encloses(Class))
        return D;
      llvm_unreachable("Class injection not implemented");
    }
  }
}

Decl *MetaclassInjector::TransformVarDecl(VarDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  VarDecl *R = VarDecl::Create(SemaRef.Context, SemaRef.CurContext,  
                               D->getLocation(), D->getLocation(), 
                               D->getIdentifier(), TypeInfo->getType(), 
                               TypeInfo, D->getStorageClass());
  transformedLocalDecl(D, R);

  // FIXME: Other attributes to translate?
  
  SemaRef.CurContext->addDecl(R);

  // Transform the initializer.
  // FIXME: Look at Sema::InstantiateVariableInitializer to see how this
  // should be done.
  if (D->getInit()) {
    VarDecl::InitializationStyle InitStyle = D->getInitStyle();
    ExprResult Init = TransformInitializer(D->getInit(),
                                           InitStyle == VarDecl::CallInit);
    if (Init.isInvalid()) {
      R->setInvalidDecl();
    } else {
      R->setInitStyle(InitStyle);
      R->setInit(Init.get());
    }
  }

  return R;
}

// FIXME: Register parameters as locally transformed entities? Probably.
Decl *MetaclassInjector::TransformParmVarDecl(ParmVarDecl *D) {
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

/// Translate static methods inside of a class.
Decl *MetaclassInjector::TransformFunctionDecl(FunctionDecl *D) {
  DeclarationNameInfo NameInfo = 
    TransformDeclarationNameInfo(D->getNameInfo());
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  FunctionDecl *R = FunctionDecl::Create(SemaRef.Context, SemaRef.CurContext, 
                                         D->getLocation(), 
                                         NameInfo.getLoc(), 
                                         NameInfo.getName(),
                                         TypeInfo->getType(), TypeInfo,
                                         D->getStorageClass(),
                                         D->isInlineSpecified(),
                                         D->hasWrittenPrototype(),
                                         D->isConstexpr());
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

Decl *MetaclassInjector::TransformCXXMethodDecl(CXXMethodDecl *D) {
  DeclarationNameInfo NameInfo = 
    TransformDeclarationNameInfo(D->getNameInfo());

  // FIXME: The exception specification is not being translated correctly
  // for destructors (probably others).
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());

  // FIXME: Handle conversion operators.
  CXXRecordDecl *CurClass = cast<CXXRecordDecl>(SemaRef.CurContext);
  CXXMethodDecl *R;
  if (auto *Ctor = dyn_cast<CXXConstructorDecl>(D))
    R = CXXConstructorDecl::Create(SemaRef.Context, CurClass, 
                                   D->getLocation(), NameInfo, 
                                   TypeInfo->getType(), TypeInfo,
                                   Ctor->isExplicitSpecified(),
                                   Ctor->isInlineSpecified(), 
                                   /*isImplicitlyDeclared=*/false,
                                   Ctor->isConstexpr(),
                                   InheritedConstructor());
  else if (isa<CXXDestructorDecl>(D))
    R = CXXDestructorDecl::Create(SemaRef.Context, CurClass, 
                                  D->getLocation(), NameInfo, 
                                  TypeInfo->getType(), TypeInfo, 
                                  D->isInlineSpecified(), 
                                  /*isImplicitlyDeclared=*/false);
  else
    R = CXXMethodDecl::Create(SemaRef.Context, CurClass, 
                              D->getLocStart(), NameInfo, 
                              TypeInfo->getType(), TypeInfo,
                              D->getStorageClass(), D->isInlineSpecified(),
                              D->isConstexpr(), D->getLocEnd());
  transformedLocalDecl(D, R);

  TransformFunctionParameters(D, R);

  // FIXME: What other properties do I need to set?
  R->setAccess(D->getAccess()); // FIXME: Is this right?
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

Decl * MetaclassInjector::TransformCXXConstructorDecl(CXXConstructorDecl *D) {
  return TransformCXXMethodDecl(D);
}

Decl * MetaclassInjector::TransformCXXDestructorDecl(CXXDestructorDecl *D) {
  return TransformCXXMethodDecl(D);
}

Decl *MetaclassInjector::TransformFieldDecl(FieldDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  FieldDecl *R = FieldDecl::Create(SemaRef.Context, SemaRef.CurContext, 
                                   D->getLocation(), D->getLocation(), 
                                   D->getIdentifier(), 
                                   TypeInfo->getType(), TypeInfo,
                                   /*Bitwidth*/nullptr, D->isMutable(), 
                                   D->getInClassInitStyle());

  transformedLocalDecl(D, R);
  
  // FIXME: What other properties do we need to copy?
  R->setAccess(D->getAccess()); // FIXME: Is this right?
  
  SemaRef.CurContext->addDecl(R);

  // FIXME: Transform the initializer, if present.
  return R;
}

Decl *MetaclassInjector::TransformConstexprDecl(ConstexprDecl *D) {
  // We can use the ActOn* members since the initial parsing for these
  // declarations is trivial (i.e., don't have to translate declarators).
  int F; // Unused
  DeclResult New = SemaRef.ActOnStartConstexprDeclaration(D->getLocation(), F);
  ConstexprDecl *R = cast<ConstexprDecl>(New.get());
  SemaRef.ActOnStartOfConstexprDef(R);
  StmtResult S = TransformStmt(D->getBody());
  if (S.isInvalid())
    R->setInvalidDecl();
  else
    SemaRef.ActOnFinishConstexprDeclaration(R, S.get());
  return R;
}

// Transform each parameter in turn.
void MetaclassInjector::TransformFunctionParameters(FunctionDecl *D,
                                                    FunctionDecl *R) {
  llvm::SmallVector<ParmVarDecl *, 4> Params;
  for (auto Iter = D->param_begin(); Iter != D->param_end(); ++Iter) {
    ParmVarDecl *P = cast<ParmVarDecl>(TransformDecl(*Iter));
    P->setOwningFunction(R);
    Params.push_back(P);
  }
  R->setParams(Params);
}

// Transform the body of the function.
void MetaclassInjector::TransformFunctionDefinition(FunctionDecl *D, 
                                                    FunctionDecl *R) {
  // Transform the method definition.
  if (Stmt *S = D->getBody()) {
    // Set up the semantic context needed to translate the function. We don't 
    // use PushDeclContext because we don't have a scope.
    EnterExpressionEvaluationContext EvalContext(SemaRef,
                                                 Sema::PotentiallyEvaluated);
    SemaRef.ActOnStartOfFunctionDef(nullptr, R);

    Sema::ContextRAII SavedContext(SemaRef, R);
    StmtResult Body = TransformStmt(S);
    if (Body.isInvalid()) {
      // FIXME: Diagnose a transformation error?
      R->setInvalidDecl();
      return;
    }
    SemaRef.ActOnFinishFunctionBody(R, Body.get());
    SavedContext.pop();
  }
}

/// Copy, by way of transforming, the members of the given metaclass into
/// the target class. 
///
/// The Fields parameter is used to store injected fields for subsequent 
/// analysis by ActOnFields.
///
/// Note that this is always called within the scope of the receiving class,
/// as if the declarations were being written in place.
void Sema::InjectMetaclassMembers(MetaclassDecl *Meta, CXXRecordDecl *Class,
                                  SmallVectorImpl<Decl *> &Fields)
{
  llvm::outs() << "INJECT MEMBERS\n";
  Meta->dump();

  // Make the receiving class the top-level context.
  Sema::ContextRAII SavedContext(*this, Class);

  // Inject each metaclass member in turn.
  CXXRecordDecl *Def = Meta->getDefinition();
  for (Decl *D : Def->decls()) {
    if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(D)) {
      // Skip the injected class name.
      if (RD->isInjectedClassName())
        continue;
    }
    
    // Inject the declaration into the class. The injection site is the
    // closing brace of the class body.
    MetaclassInjector Inject(*this, Def, Class);
    if (Decl *R = Inject.TransformDecl(D)) {
      if (isa<FieldDecl>(R))
        Fields.push_back(R);
    }
  }
  llvm::outs() << "RESULTING CLASS\n";
  Class->dump();
}

// Try to apply a request to modify access.
static bool InjectAccessModification(Sema& SemaRef, ReflectionTraitExpr *E) {
  llvm::outs() << "ACCESS\n";
  E->dump();
  return true;
}

// Try to apply a request to make a member function virtual or non-virtual.
static bool InjectVirtualModification(Sema& SemaRef, ReflectionTraitExpr *E) {
  llvm::outs() << "VIRTUAL\n";
  E->dump();
  return true;
} 

/// Apply one injection. Returns true if no error is encountered.
bool Sema::InjectCode(Stmt *Injection) {
  switch (Injection->getStmtClass()) {
    case Stmt::ReflectionTraitExprClass: {
      ReflectionTraitExpr *E = cast<ReflectionTraitExpr>(Injection);
      switch (E->getTrait()) {
        case BRT_ModifyAccess:
          return InjectAccessModification(*this, E);
        case BRT_ModifyVirtual:
          return InjectVirtualModification(*this, E);
        default:
          llvm_unreachable("Invalid reflection trait");
      }
    }
    default:
      break;
  }
  llvm_unreachable("Invalid injection");
}

/// Inject a sequence of source code fragments or modification requests
/// into the current AST. Returns false if an error is encountered.
bool Sema::InjectCode(SmallVectorImpl<Stmt *>& Injections) {
  for (Stmt *S : Injections)
    if (!InjectCode(S))
      return false;
    return true;
}

