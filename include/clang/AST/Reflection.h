//===--- ASTContext.h - Context to hold long-lived AST nodes ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief Defines facilities for static reflection.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_AST_REFLECTION_H
#define LLVM_CLANG_AST_REFLECTION_H

#include "clang/AST/Type.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "llvm/ADT/PointerSumType.h"

namespace clang {


/// \brief The kind of source code construct reflected.
///
/// This value is packed into the low-order bits of each reflected pointer.
enum ReflectionKind { 
  RK_Decl = 1, 
  RK_Type = 2, 
  RK_Expr = 3 
};



#if 0
// /// An expanded reflection value.
// using ReflectionPair = std::pair<ReflectionKind, void *>;

// /// Returns a pair containing the reflection kind and AST node pointer.
// inline ReflectionPair ExplodeReflectionValue(std::uintptr_t N) {
//   using Helper = llvm::detail::PointerSumTypeHelper<
//       ReflectionKind, 
//       llvm::PointerSumTypeMember<RK_Decl, Decl *>,
//       llvm::PointerSumTypeMember<RK_Type, Type *>,
//       llvm::PointerSumTypeMember<RK_Expr, Expr *>>;
//   ReflectionKind K = (ReflectionKind)(N & Helper::TagMask);
//   void *P = (void *)(N & Helper::PointerMask);
//   return {K, P};
// }

/// An encoded 
class Reflection {
private:
  /// \brief Used to encode the kind of source code construct reflected.
  /// These value is packed into the low-order bits of a pointer union in order
  /// to provide a single intptr-wide node representation.
  enum ReflectionKind { 
    RK_Null = 0,
    RK_Decl = 1, 
    RK_Type = 2, 
    RK_Expr = 3 
  };

  /// The opaque representation of a node reflection.
  using ReflectionValue =
      llvm::PointerSumType<ReflectionKind,
                           llvm::PointerSumTypeMember<RK_Null, void *>,
                           llvm::PointerSumTypeMember<RK_Decl, Decl *>,
                           llvm::PointerSumTypeMember<RK_Type, Type *>,
                           llvm::PointerSumTypeMember<RK_Expr, Expr *>>;

  /// The reflected construct (entity + expression).
  ReflectionValue Val;

public:
  Reflection() 
    : Val() { }

  Reflection(Decl *D)
    : Val(ReflectionValue::create<RK_Decl>(D)) { }

  Reflection(Type *T)
    : Val(ReflectionValue::create<RK_Type>(T)) { }

  Reflection(Expr *E)
    : Val(ReflectionValue::create<RK_Expr>(E)) { }

  Reflection(std::intptr_t N) {
      using Helper = llvm::detail::PointerSumTypeHelper<
          ReflectionKind, 
          llvm::PointerSumTypeMember<RK_Decl, Decl *>,
          llvm::PointerSumTypeMember<RK_Type, Type *>,
          llvm::PointerSumTypeMember<RK_Expr, Expr *>>;
      ReflectionKind K = (ReflectionKind)(N & Helper::TagMask);
      void *P = (void *)(N & Helper::PointerMask);
      switch (K) {
        case RK_Null:
          Val = ReflectionValue(); 
          break;
        case RK_Decl: return Reflection((Decl*)P);
        case RK_Type: return Reflection((Type*)P);
        case RK_Expr: return Reflection((Expr*)P);
      }

  }
  static ReflectionValue fromOpaqueValue(std::intptr_t N) {
      using Helper = llvm::detail::PointerSumTypeHelper<
          ReflectionKind, 
          llvm::PointerSumTypeMember<RK_Decl, Decl *>,
          llvm::PointerSumTypeMember<RK_Type, Type *>,
          llvm::PointerSumTypeMember<RK_Expr, Expr *>>;
      ReflectionKind K = (ReflectionKind)(N & Helper::TagMask);
      void *P = (void *)(N & Helper::PointerMask);
      switch (K) {
        case RK_Null: return Reflection();
        case RK_Decl: return Reflection((Decl*)P);
        case RK_Type: return Reflection((Type*)P);
        case RK_Expr: return Reflection((Expr*)P);
      }
    }
  }
  
  #if 0
  explicit ReflectedConstruct(std::uintptr_t V) 
    : Valid(true), P(ExplodeOpaqueValue(V)) { }

  /// \brief Returns true if the reflection is valid.
  bool isValid() const { return Valid; }

  /// \brief Returns true if the reflection is invalid.
  bool isInvalid() const { return !Valid; }

  /// \brief Converts to true when the reflection is valid.
  explicit operator bool() const { return Valid; }

  /// \brief Returns true if this is a declaration.
  bool isDeclaration() const { return P.first == RK_Decl; }
  
  /// \brief Returns true if this is a type reflection.
  bool isType() const { return P.first == RK_Type; }

  /// \brief The reflected declaration or nullptr if not a declaration.
  Decl *getAsDeclaration() {
    return isDeclaration() ? (Decl *)P.second : nullptr;
  }

  /// \brief The reflected type or nullptr if not a type.
  Type *getAsType() {
    return isType() ? (Type *)P.second : nullptr;
  }
  #endif
};
#endif

} // namespace clang

#endif
