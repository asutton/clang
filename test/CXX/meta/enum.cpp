// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

// FIXME: This can't work with our current model of application. We need
// to inject into a new class.

$class basic_enum {
  constexpr {
    compiler.require($prototype.member_variables().size() > 0, 
      "an enum cannot be empty");

    // Determine the underlying type.
    auto type = get<0>($prototype.member_variables()).type();
    -> class { 
      using underlying_type = typename(type); 
    };

    // Check other properties.
    //
    // Do they also need to be defined?
    for... (auto m : $basic_enum.member_variables()) {
      compiler.require(m.is_public(), "enumerators must be public");
      compiler.require(m.type() == type, "enumerators must have the same type");
    }

    int value = 0;
    for... (auto m : $prototype.member_variables()) {
      -> class {
        static constexpr typename(type) idexpr(m) = value;
      };
      ++value;
    }
  }

  // Make enumerators constexr.
  constexpr {
  }
};

basic_enum my_enum {
  int a, b, c;
};


int main() {
  compiler.debug($my_enum);
}
