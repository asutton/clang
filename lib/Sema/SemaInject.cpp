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

  Decl *TransformDecl(Decl *D);
  Decl *TransformDecl(SourceLocation, Decl *D);
  Decl *TransformParmVarDecl(ParmVarDecl *D);
  Decl *TransformCXXMethodDecl(CXXMethodDecl *D);
  Decl *TransformCXXConstructorDecl(CXXConstructorDecl *D);
  Decl *TransformCXXDestructorDecl(CXXDestructorDecl *D);
};

/// Look to see if the declaration has been locally transformed. If so,
/// return that. Otherwise, explicitly rebuild the declaration.
Decl *MetaclassInjector::TransformDecl(Decl *D) {
  return TransformDecl(D->getLocation(), D);
}

/// Look to see if the declaration has been locally transformed. If so,
/// return that. Otherwise, explicitly rebuild the declaration.
Decl *MetaclassInjector::TransformDecl(SourceLocation Loc, Decl *D) {
  llvm::DenseMap<Decl *, Decl *>::iterator Known
    = TransformedLocalDecls.find(D);
  if (Known != TransformedLocalDecls.end())
    return Known->second;

  /// FIXME: It might be a better idea to use a DeclVisitor here.
  switch (D->getKind()) {
    default:
      llvm::errs() << "SKIPPING: " << D->getDeclKindName() << '\n';
      return nullptr;
    case Decl::ParmVar:
      return TransformParmVarDecl(cast<ParmVarDecl>(D));
    case Decl::CXXMethod:
      return TransformCXXMethodDecl(cast<CXXMethodDecl>(D));
    case Decl::CXXConstructor:
      return TransformCXXConstructorDecl(cast<CXXConstructorDecl>(D));
    case Decl::CXXDestructor:
      return TransformCXXDestructorDecl(cast<CXXDestructorDecl>(D));
  }
}

Decl *MetaclassInjector::TransformParmVarDecl(ParmVarDecl *D) {
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());
  auto *R = SemaRef.CheckParameter(SemaRef.Context.getTranslationUnitDecl(),
                                   D->getInnerLocStart(), D->getLocation(),
                                   D->getIdentifier(), TypeInfo->getType(), 
                                   TypeInfo, D->getStorageClass());
  // FIXME: Transform the default argument also.
  return R;
}

Decl *MetaclassInjector::TransformCXXMethodDecl(CXXMethodDecl *D) {
  DeclarationNameInfo NameInfo = 
    TransformDeclarationNameInfo(D->getNameInfo());

  // FIXME: The exception specification is not being translated correctly
  // for destructors (probably others).
  TypeSourceInfo *TypeInfo = TransformType(D->getTypeSourceInfo());

  CXXMethodDecl *R;
  if (isa<CXXConstructorDecl>(D))
    assert(false && "not implemented");
    // R = CXXConstructorDecl::Create(SemaRef.Context, Dest, D->getLocation(),
    //                                   NameInfo, TypeInfo->getType(), TypeInfo,
    //                                   D->isInlineSpecified(), false);

  else if (isa<CXXDestructorDecl>(D))
    R = CXXDestructorDecl::Create(SemaRef.Context, Dest, D->getLocation(),
                                      NameInfo, TypeInfo->getType(), TypeInfo,
                                      D->isInlineSpecified(), false);
  else
    R = CXXMethodDecl::Create(SemaRef.Context, Dest, D->getLocStart(),
                              NameInfo, TypeInfo->getType(), TypeInfo,
                              D->getStorageClass(), D->isInlineSpecified(),
                              D->isConstexpr(), D->getLocEnd());

  // Copy over common attributes.
  R->setDefaulted(D->isDefaulted());
  R->setExplicitlyDefaulted(D->isExplicitlyDefaulted());
  R->setDeletedAsWritten(D->isDeletedAsWritten());
  R->setVirtualAsWritten(D->isVirtualAsWritten());

  // Transform parameters
  llvm::SmallVector<ParmVarDecl *, 4> Params;
  for (auto Iter = D->param_begin(); Iter != D->param_end(); ++Iter) {
    ParmVarDecl *P = cast<ParmVarDecl>(TransformDecl(*Iter));
    P->setOwningFunction(R);
    Params.push_back(P);
  }
  R->setParams(Params);

  // TODO: Transform the body of the declaration.

  // FIXME: Handle redeclaration, update w.r.t. virtual functions, etc.
  Dest->addDecl(R);
  return R;
}

Decl * MetaclassInjector::TransformCXXConstructorDecl(CXXConstructorDecl *D) {
  return TransformCXXMethodDecl(D);
}

Decl * MetaclassInjector::TransformCXXDestructorDecl(CXXDestructorDecl *D) {
  return TransformCXXMethodDecl(D);
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
  CXXRecordDecl *Def = Meta->getDefinition();
  for (Decl *D : Def->decls()) {
    if (CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(D)) {
      // Skip the injected class name.
      if (RD->isInjectedClassName())
        continue;
    }
    
    // Inject the declaration into the class. The injection site is the
    // closing brace of the class body.
    //
    // FIXME: Do something with the result?
    MetaclassInjector Inject(*this, Def, Class);
    if (Decl *R = Inject.TransformDecl(D)) {
      if (isa<FieldDecl>(R))
        Fields.push_back(R);
    }
  }
  Class->dump();
}
