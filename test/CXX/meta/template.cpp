// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

#include <string>

using namespace cppx;

constexpr void f1() {
  __generate __fragment struct {
    template<typename T>
    T id(T x) { return x; }
  };
}

template<typename T>
constexpr void f2() {
  __generate __fragment struct {
    template<typename U>
    T make_t(U arg) { return T{arg}; }
  };

  __generate __fragment struct {
    template<typename... Args>
    T make_with_args(Args... args) {
      std::tuple<Args...> tup;
      return T{};
    }
  };
}


struct S {
  constexpr {
    f1();
    f2<int>();
  }
};

constexpr {
  meta::compiler.debug($S);
}


int main() {
  S s;
  s.id(0);
  s.make_t(0);
  s.make_with_args(1);
}
