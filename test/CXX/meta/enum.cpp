// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

// FIXME: This can't work with our current model of application. We need
// to inject into a new class.

$class basic_enum {
  constexpr {
    compiler.require($basic_enum.member_variables().size() > 0, 
      "an enum cannot be empty");

    // Determine the underlying type.
    auto type = get<0>($basic_enum.member_variables()).type();
    -> [type] class { 
      using underlying_type = typename(type); 
    }

    // Check other properties.
    //
    // Do they also need to be defined?
    for... (auto m : $basic_enum.member_variables()) {
      compiler.require(m.is_public(), "enumerators must be public");
      compiler.require(m.type() == type, "enumerators must have the same type");
    }
  }

  // Make enumerators constexr.
  constexpr {
    for... (auto m : $basic_enum.member_variables())
      m.make_constexpr();
  }

  //   for (auto o : $basic_enum.member_variables()) {
  //      if (!o.has_access())   o.make_public();
  //      if (!o.has_storage())  o.make_constexpr();
  //      if (o.has_auto_type()) o.set_type(U);
  //      compiler.require(o.is_public(),    "enumerators must be public");
  //      compiler.require(o.is_constexpr(), "enumerators must be constexpr");
  //      compiler.require(o.type() == U,    "enumerators must use same type");
  //   }
  //   -> { U$ value; }        // the instance value
  // }
};

basic_enum my_enum {
  int a = 0;
  int b = 1;
};


int main() {
  compiler.debug($my_enum);
}
