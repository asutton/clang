// -*- C++ -*-

#ifndef CPPX_TRAITS_HPP
#define CPPX_TRAITS_HPP

#include <cassert>
#include <cstdint>


namespace cppx
{
namespace meta
{
inline namespace v1
{

// -------------------------------------------------------------------------- //
// Specifiers and traits
//
// NOTE: These order and structure of the _info classes needs to be kept in 
// sync with the compiler.

enum linkage_kind : unsigned {
  no_linkage,
  internal_linkage,
  external_linkage
};

// The linkage of a bitfield is always stored in the first 2 bits.
static constexpr linkage_kind get_linkage(unsigned n) {
  return linkage_kind(n & 0x03);
}

enum access_kind : unsigned {
  no_access,
  public_access,
  private_access,
  protected_access,
};

// Access specifiers are always stored in bits 3 and 4.
static constexpr access_kind get_access(unsigned n) {
  return access_kind((n & 0x0b) >> 2);
}

enum storage_kind : unsigned {
  no_storage,
  static_storage,
  automatic_storage,
  thread_storage,
};

// When present, storage specifiers are stored in bits 5 and 6.
static constexpr storage_kind get_storage(unsigned n) {
  return storage_kind((n & 0x0b) >> 2);
}

// All declarations have linkage and access.
struct decl_traits {
  constexpr explicit decl_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n))   // 0x04 | 0x08
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
};

struct variable_traits {
  constexpr explicit variable_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n)),  // 0x04 | 0x08
      storage      (get_storage(n)), // 0x10 | 0x20
      is_constexpr (n & 0x40),
      is_defined   (n & 0x80),
      is_inline    (n & 0x0100)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  storage_kind storage : 2;
  bool is_constexpr : 1;
  bool is_defined : 1;
  bool is_inline : 1;
};

struct function_traits {
  constexpr explicit function_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n)),  // 0x04 | 0x08
      is_constexpr (n & 0x10),
      is_noexcept  (n & 0x20),
      is_defined   (n & 0x40),
      is_inline    (n & 0x80),
      is_deleted   (n & 0x0100)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  bool is_constexpr : 1;
  bool is_noexcept : 1;
  bool is_defined : 1;
  bool is_inline : 1;
  bool is_deleted : 1;
};

struct value_traits {
  constexpr explicit value_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n))   // 0x04 | 0x08
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
};

struct namespace_traits {
  constexpr explicit namespace_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n)),  // 0x04 | 0x08
      is_inline    (n & 0x10)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  bool is_inline : 1;
};

struct field_traits {
  constexpr explicit field_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n)),  // 0x04 | 0x08
      storage      (get_storage(n)), // 0x10 | 0x20
      is_mutable   (n & 0x40)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  storage_kind storage : 2;
  bool is_mutable : 1;
};

struct method_traits {
  constexpr explicit method_traits(unsigned n)
    : linkage      (get_linkage(n)), // 0x01 | 0x02
      access       (get_access(n)),  // 0x04 | 0x08
      is_constexpr (n & 0x10),
      is_explicit  (n & 0x20),
      is_virtual   (n & 0x40),
      is_pure      (n & 0x80),
      is_final     (n & 0x0100),
      is_override  (n & 0x0200),
      is_noexcept  (n & 0x0400),
      is_defined   (n & 0x0800),
      is_inline    (n & 0x1000),
      is_deleted   (n & 0x2000),
      is_defaulted (n & 0x4000),
      is_trivial   (n & 0x8000)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  bool is_constexpr : 1; // not dtors
  bool is_explicit : 1; // ctors and conversions
  bool is_virtual : 1; // not ctors
  bool is_pure : 1; // not ctors
  bool is_final : 1; // not ctors
  bool is_override : 1; // not ctors
  bool is_noexcept : 1;
  bool is_defined : 1;
  bool is_inline : 1;
  bool is_deleted : 1;
  bool is_defaulted : 1; // ctors and dtors
  bool is_trivial : 1; // ctors and dtors
};


// TODO: Accumulate all known type traits for classes.
struct class_traits {
  constexpr explicit class_traits(unsigned n)
    : linkage       (get_linkage(n)), // 0x01 | 0x02
      access        (get_access(n)),  // 0x04 | 0x08
      is_complete   (n & 0x10),
      is_polymorphic(n & 0x20),
      is_abstract   (n & 0x40),
      is_final      (n & 0x80),
      is_empty      (n & 0x0100)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  bool is_complete : 1;
  bool is_polymorphic : 1;
  bool is_abstract : 1;
  bool is_final : 1;
  bool is_empty : 1;
};


struct enum_traits {
  constexpr explicit enum_traits(unsigned n)
    : linkage    (get_linkage(n)), // 0x01 | 0x02
      access     (get_access(n)),  // 0x04 | 0x08
      is_scoped  (n & 0x10),
      is_complete(n & 0x20)
  { }

  linkage_kind linkage : 2;
  access_kind access : 2;
  bool is_scoped;
  bool is_complete;
};

} // inline namespace v1
} // namespace meta
} // namespace cppx


#endif // CPPX_TRAITS_HPP
