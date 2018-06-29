// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;


constexpr auto frag = __fragment namespace N {
  int n = 42;
  int f() { return n + 3; }

  namespace X {
    int m = 17;
    int g() { return n + m; }
  }
};

constexpr {
  __generate frag;
}


int main() {
  f();
  assert(n == 42);
  assert(f() == 45);
  assert(X::m == 17);
  assert(X::g() == n + X::m);
}
