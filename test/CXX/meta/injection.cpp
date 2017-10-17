// RUN: %clang -std=c++1z -Xclang -freflection -Xclang -verify %s 

// FIXME: This compiles, but fails to link. Using _cc1 causes this to
// not find standard headers (we could remove <cassert> from the lib).

#include <cppx/meta>

constexpr {
  __generate class C { }; 
} // expected-error{{injecting class members into global scope}}

int main() { }
