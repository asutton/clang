//===--- ExprConstant.cpp - Expression Constant Evaluator -----------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the Reflect method of various AST nodes. 
// 
// Reflection returns builds an APValue storing the compile-time representation 
// of reflected attributes.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/APValue.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTDiagnostic.h"
#include "clang/AST/ASTLambda.h"
#include "clang/AST/CharUnits.h"
#include "clang/AST/Expr.h"
#include "clang/AST/RecordLayout.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/AST/TypeLoc.h"
#include "clang/Basic/Builtins.h"
#include "clang/Basic/TargetInfo.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/raw_ostream.h"
#include <cstring>
#include <functional>

using namespace clang;
using llvm::APSInt;
using llvm::APFloat;


namespace {

llvm::APSInt
GetLinkage(ASTContext &C, QualType T, ValueDecl *D) {
  Linkage L = D->getFormalLinkage();
  if (L == NoLinkage)
    return C.MakeIntValue(0, T);
  if (L == InternalLinkage)
    return C.MakeIntValue(1, T);
  else
    return C.MakeIntValue(2, T);
}


} // end namespace

// TODO: I don't like the name of this function. I also don't like how
// it works. Maybe it should be virtual to avoid the explicit casts below.
bool
ValueDecl::Reflect(ASTContext &C, const Expr *E, std::uint64_t N, APValue &R) {
  switch (N) {
    case RAI_Linkage: 
      R = APValue(GetLinkage(C, E->getType(), this));
      return true;

    // TODO: Implement me.
    case RAI_Storage:
    case RAI_Constexpr:
    case RAI_Inline:
    case RAI_Virtual:
    case RAI_Type:
      llvm_unreachable("Unhandled attribute selector");
      break;

    case RAI_Parameters: {
      if (FunctionDecl* F = dyn_cast<FunctionDecl>(this)) {
        R = APValue(C.MakeIntValue(F->getNumParams(), C.getSizeType()));
        return true;
      }
      break;
    }
    default:
      break; 
  }
  llvm_unreachable("Unknown attribute selector");
  return false;
}

