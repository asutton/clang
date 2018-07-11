// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;


constexpr auto generate_ns() {
  auto f = __fragment namespace N {
    int n = 42;
    int g() { return n; }

    namespace X {
      int m = 17;
      int h() { return m + n; }
    }
  };
  return f;
}

constexpr {
  __generate generate_ns();
}


int main() {
  assert(n == 42);
  assert(g() == 42);
  assert(X::m == 17);
  assert(X::h() == 42 + 17);
}
