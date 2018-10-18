// RUN: %clang -c -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>

using namespace cppx;

template<typename T>
constexpr void foo(T arg) {
  int n = 0;
  for... (auto x : arg.member_functions()) {
    x.set_name(__concatenate(x.name(), "_version_", n));
    __generate x;
  }
}

class(foo) Blah {
  void f() { }
};

constexpr {
  compiler.debug($Blah);
}
