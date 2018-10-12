//===--- TypeTraits.h - C++ Type Traits Support Enumerations ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief Defines enumerations for the type traits support.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_BASIC_TYPETRAITS_H
#define LLVM_CLANG_BASIC_TYPETRAITS_H

namespace clang {

  /// \brief Names for traits that operate specifically on types.
  enum TypeTrait {
    UTT_HasNothrowAssign,
    UTT_HasNothrowMoveAssign,
    UTT_HasNothrowCopy,
    UTT_HasNothrowConstructor,
    UTT_HasTrivialAssign,
    UTT_HasTrivialMoveAssign,
    UTT_HasTrivialCopy,
    UTT_HasTrivialDefaultConstructor,
    UTT_HasTrivialMoveConstructor,
    UTT_HasTrivialDestructor,
    UTT_HasVirtualDestructor,
    UTT_IsAbstract,
    UTT_IsAggregate,
    UTT_IsArithmetic,
    UTT_IsArray,
    UTT_IsClass,
    UTT_IsCompleteType,
    UTT_IsCompound,
    UTT_IsConst,
    UTT_IsDestructible,
    UTT_IsEmpty,
    UTT_IsEnum,
    UTT_IsFinal,
    UTT_IsFloatingPoint,
    UTT_IsFunction,
    UTT_IsFundamental,
    UTT_IsIntegral,
    UTT_IsInterfaceClass,
    UTT_IsLiteral,
    UTT_IsLvalueReference,
    UTT_IsMemberFunctionPointer,
    UTT_IsMemberObjectPointer,
    UTT_IsMemberPointer,
    UTT_IsNothrowDestructible,
    UTT_IsObject,
    UTT_IsPOD,
    UTT_IsPointer,
    UTT_IsPolymorphic,
    UTT_IsReference,
    UTT_IsRvalueReference,
    UTT_IsScalar,
    UTT_IsSealed,
    UTT_IsSigned,
    UTT_IsStandardLayout,
    UTT_IsTrivial,
    UTT_IsTriviallyCopyable,
    UTT_IsUnion,
    UTT_IsUnsigned,
    UTT_IsVoid,
    UTT_IsVolatile,
    UTT_Last = UTT_IsVolatile,
    BTT_IsBaseOf,
    BTT_IsConvertible,
    BTT_IsConvertibleTo,
    BTT_IsSame,
    BTT_TypeCompatible,
    BTT_IsAssignable,
    BTT_IsNothrowAssignable,
    BTT_IsTriviallyAssignable,
    BTT_Last = BTT_IsTriviallyAssignable,
    TT_IsConstructible,
    TT_IsNothrowConstructible,
    TT_IsTriviallyConstructible
  };

  /// \brief Names for the array type traits.
  enum ArrayTypeTrait {
    ATT_ArrayRank,
    ATT_ArrayExtent
  };

  /// \brief Names for the "expression or type" traits.
  enum UnaryExprOrTypeTrait {
    UETT_SizeOf,
    UETT_AlignOf,
    UETT_VecStep,
    UETT_OpenMPRequiredSimdAlign,
  };

  /// \brief Names for reflectors.
  /// 
  /// Unary reflectors (prefixed by 'U') take a single argument, an expression
  /// yielding a reflected node, while binary reflectors (prefixed by 'B') take
  /// two arguments, both expressions. The first is the reflected node, and the
  /// second is usually an integer value that indexes into an array.
  enum ReflectionTrait {
    URT_ReflectPrint, ///< Emits debug info about a reflection.
    URT_ReflectName,
    URT_ReflectQualifiedName,
    URT_ReflectDeclarationContext,
    URT_ReflectLexicalContext,
    URT_ReflectTraits, ///< Computed properties of declarations.
    URT_ReflectDefaultAccess, ///< True if an entity has default access.
    URT_ReflectSpecifiers, ///< Written properties of declarations.
    
    URT_ReflectType,
    URT_ReflectPointer, ///< For stored values.
    URT_ReflectValue, ///< For named values
    
    URT_ReflectNumParameters,
    BRT_ReflectParameter,
    URT_ReflectReturn,
    URT_ReflectNumMembers,
    BRT_ReflectMember,
    URT_ReflectNumBases,
    BRT_ReflectBase,

    BRT_ModifyAccess,  ///< Second operand indicates access level.
    BRT_ModifyVirtual, ///< Second operand is \c true to indicate pure virtual.
    URT_ModifyConstexpr
  };
}

#endif
