// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

#include <cassert>

struct S { 
  __inject struct { int y; };
};

__extend ($S) struct { int x; };
__extend ($S) struct { void foobar() { } };

constexpr auto mz = __fragment struct { int z; };
__extend ($S) mz;

struct T {
  int f(int n) { return n + 1; }
};

constexpr auto f = $T::f;
__extend ($S) f;

int
main() {

  compiler.debug($S);
}
