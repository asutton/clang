// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

constexpr auto f() {
  __generate __fragment struct {
    template<typename T>
    T id(T x) { return x; }
  };
}


struct S {
  constexpr {
    f();
  }
  // template<typename T>
  // T id(T x) { return x; }
};

constexpr {
  meta::compiler.debug($S);
}


int main() {
  S s;
  s.id(0);
}