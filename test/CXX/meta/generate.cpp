// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>

// constexpr {
//   int n = 42;
  
//   auto x = __fragment namespace N1 {
//     int a = n;
//     int b = n + 2;
//     int c = n / 4;

//     int f() { return 0; }
//   };

//   // Writes N1 members into the enclosing namespace.
//   __generate x;

//   // Writes the following members into the enclosing namespace.
//   __generate namespace N2 {
//     int q = 32;
//   };
// }

// // Make sure we actually get definitions of these things.
// int test_a = a;
// int test_f = f();
// int test_q = q;

// template<typename T>
// constexpr void gen1() {
//   __generate namespace N3 {
//     T foobar;
//   };
// }

// constexpr {
//   gen1<int>();
// }

// int test_foobar = foobar;


// int global = 5;

// constexpr {
//   int p = 7;
//   char q = 49;
  
//   auto x = __fragment namespace N {
//     int foo() { return p + q; };
//   };

//   __generate x;
// }

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
        int idexpr("y", n) = 42;
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
