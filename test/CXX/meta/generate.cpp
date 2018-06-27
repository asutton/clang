// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>

enum E {
  A, B, C
  // A
};

struct S {
  constexpr {
    int n = 0;
    for... (auto x : $E.members()) {
      __generate struct {
        int idexpr("x", n) = n;
        // int idexpr("y", n) = 42;
      };
      ++n;
    }

    auto frag = __fragment struct S {
      int foo() { return 42; }
    };
    __generate frag;
  }
};

int main() {
  // assert(a == 42);
  // assert(b == 44);
  // assert(c == 10);
  // assert(f() == 0);

  S s;
  assert(s.x0 == 0);
  assert(s.x1 == 1);
  assert(s.x2 == 2);
  assert(s.foo() == 42);
}
