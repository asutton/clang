//=- Lifetime.h - Diagnose lifetime violations -*- C++ -*-====================//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIME_H
#define LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIME_H

#include "clang/Basic/OperatorKinds.h"
#include "clang/Basic/SourceLocation.h"
#include <string>
#include "llvm/ADT/STLExtras.h"

namespace clang {
class FunctionDecl;
class ASTContext;
class SourceManager;
class VarDecl;
class Sema;
class QualType;
class ClassTemplateSpecializationDecl;
class CXXRecordDecl;
class FunctionDecl;

namespace lifetime {
enum class TypeCategory { Owner, Pointer, Aggregate, Value };

using LookupOperatorTy = llvm::function_ref<FunctionDecl *(
    const CXXRecordDecl *R, OverloadedOperatorKind Op)>;
extern LookupOperatorTy GlobalLookupOperator;

using LookupMemberFunctionTy =
    llvm::function_ref<FunctionDecl *(const CXXRecordDecl *R, StringRef Name)>;
extern LookupMemberFunctionTy GlobalLookupMemberFunction;

using DefineClassTemplateSpecializationTy =
    llvm::function_ref<void(ClassTemplateSpecializationDecl *Specialization)>;
extern DefineClassTemplateSpecializationTy
    GlobalDefineClassTemplateSpecialization;

using IsConvertibleTy = llvm::function_ref<bool(QualType, QualType)>;

class LifetimeReporterBase {
public:
  virtual ~LifetimeReporterBase() = default;
  virtual void warnPsetOfGlobal(SourceLocation Loc, StringRef VariableName,
                                std::string ActualPset) = 0;
  virtual void warnDerefDangling(SourceLocation Loc, bool possibly) = 0;
  virtual void warnDerefNull(SourceLocation Loc, bool possibly) = 0;
  virtual void warnParametersAlias(SourceLocation LocParam1,
                                   SourceLocation LocParam2,
                                   const std::string &Pointee) = 0;
  virtual void warnParameterDangling(SourceLocation Loc, bool indirectly) = 0;
  virtual void warnParameterNull(SourceLocation Loc, bool possibly) = 0;
  virtual void warnReturnDangling(SourceLocation Loc, bool possibly) = 0;
  virtual void warnReturnNull(SourceLocation Loc, bool possibly) = 0;
  virtual void warnReturnWrongPset(SourceLocation Loc, StringRef RetPset,
                                   StringRef ExpectedPset) = 0;
  virtual void notePointeeLeftScope(SourceLocation Loc, std::string Name) = 0;
  virtual void warnNonStaticThrow(SourceLocation Loc, StringRef ThrownPset) = 0;

  virtual void noteNeverInitialized(SourceLocation Loc) = 0;
  virtual void noteTemporaryDestroyed(SourceLocation Loc) = 0;
  virtual void notePointerArithmetic(SourceLocation Loc) = 0;
  virtual void noteForbiddenCast(SourceLocation Loc) = 0;
  virtual void noteDereferenced(SourceLocation Loc) = 0;
  virtual void noteModified(SourceLocation Loc) = 0;
  virtual void noteAssigned(SourceLocation Loc) = 0;
  virtual void noteParameterNull(SourceLocation Loc) = 0;
  virtual void noteNullDefaultConstructed(SourceLocation Loc) = 0;
  virtual void noteNullComparedToNull(SourceLocation Loc) = 0;
  virtual void debugPset(SourceLocation Loc, StringRef Variable,
                         std::string Pset) = 0;
  virtual void debugTypeCategory(SourceLocation Loc, TypeCategory Category,
                                 StringRef Pointee = "") = 0;
};

void runAnalysis(
    const FunctionDecl *Func, ASTContext &Context,
    LifetimeReporterBase &Reporter, IsConvertibleTy IsConvertible,
    LookupOperatorTy LookupOperator,
    LookupMemberFunctionTy LookupMemberFunction,
    DefineClassTemplateSpecializationTy DefineClassTemplateSpecialization);
} // namespace lifetime
} // namespace clang

#endif // LLVM_CLANG_ANALYSIS_ANALYSES_LIFETIME_H
