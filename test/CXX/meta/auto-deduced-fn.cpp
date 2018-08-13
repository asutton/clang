// RUN: %clang -c -g -std=c++1z -Xclang -freflection %s 

// This test checks an error when reflected types are not
// being unwrapped to emit debug information.

#include <cppx/meta>

template<typename T>
constexpr void gen() {
  __generate struct {
    auto f() {
      return 0;
    }
  };
}

struct S {
  constexpr { gen<int>(); }
};

