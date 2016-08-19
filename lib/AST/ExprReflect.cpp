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

#if 0
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
#endif

} // end namespace


static StringLiteral*
MakeString(ASTContext& C, std::string const& Str)
{
  llvm::APSInt Size = C.MakeIntValue(Str.size() + 1, C.getSizeType());
  QualType Elem = C.getConstType(C.CharTy);
  QualType Type = C.getConstantArrayType(Elem, Size, ArrayType::Normal, 0);
  return StringLiteral::Create(C, Str, StringLiteral::Ascii, false, Type, 
                               SourceLocation());
}


// TODO: I don't like the name of this function. I also don't like how
// it works. Maybe it should be virtual to avoid the explicit casts below.
bool
ValueDecl::Reflect(ReflectionTrait Trait, 
                   APValue const* Arg, 
                   APValue &R, 
                   ReflectInfo Info) const {
  ASTContext& C = Info.Cxt;

  switch (Trait) {
  case URT_GetName: {
    // TODO: getNameAsString is deprecated
    std::string Name = getNameAsString();
    StringLiteral* Str = MakeString(C, Name);
    Expr::EvalResult Result;
    if (!Str->EvaluateAsLValue(Result, C))
      assert(false && "Evaluation of string literal failed");
    R = Result.Val;
    break;    
  }
  
  case URT_GetQualifiedName: {
    // TODO: getQualifiedNameAsString is deprecated
    std::string Name = getQualifiedNameAsString();
    StringLiteral* Str = MakeString(C, Name);
    Expr::EvalResult Result;
    if (!Str->EvaluateAsLValue(Result, C))
      assert(false && "Evaluation of string literal failed");
    R = Result.Val;
    break;
  }

  case URT_GetLinkage:
    R = APValue(C.MakeIntValue(0, C.IntTy));
    break;

  case URT_GetStorage:
    R = APValue(C.MakeIntValue(0, C.IntTy));
    break;
  
  case URT_GetNumParameters: {
    // FIXME: Don't fail quite so aggressively if this is not a function.
    // Emit an error and return false.
    const FunctionDecl *Fn = cast<FunctionDecl>(this);
    R = APValue(C.MakeIntValue(Fn->getNumParams(), C.getSizeType()));
    break;
  }

  case URT_GetType: 
    llvm_unreachable("__get_type not implemented");
    break;

  case BRT_GetParameter:
    // FIXME: Don't fail quite so aggressively if this is not a function.
    // Emit an error and return false.
    const FunctionDecl *Fn = cast<FunctionDecl>(this);

    // FIXME: Don't fail quite so aggressively here either.
    unsigned N = Arg->getInt().getExtValue();
    assert(N < Fn->getNumParams() && "Invalid parameter index");
    ParmVarDecl const* Parm = Fn->getParamDecl(0);

    // Build an aggregate with the same shape as the "parameter" type.
    //
    // TODO: This is super brittle. It would be great if e could emulate
    // the sema layer at this point. Unfortunately, we can't resolve lookups
    // at this point. We may be able to fake it, but this works for now.
    R = APValue(APValue::UninitStruct(), /*Bases*/0, /*Members*/1);
    APValue Node(C.MakeIntValue((std::intptr_t)this, C.getIntPtrType()));
    R.getStructField(0) = Node;
    break;
  }
  return true;
}

bool
ValueDecl::ReflectElement(ASTContext &C, const Expr *E, std::uint64_t N,
                          std::uint64_t K, APValue &R) {
#if 0
  switch (N) {
  case RAI_Parameters: {
    if (FunctionDecl* F = dyn_cast<FunctionDecl>(this)) {
      // TODO: This needs to be VERY carefully coordinated with the
      // meta::parameter type.
      R = APValue(APValue::UninitStruct(), 0, F->getNumParams());
      APValue Node(C.MakeIntValue((std::intptr_t)this, C.getIntPtrType()));
      R.getStructField(0) = Node;
      return true;
    }
  }
  default:
    break; 
  }
#endif
  // FIXME: Use real diagnostics.
  llvm_unreachable("Unknown attribute selector");
  return false;
}
