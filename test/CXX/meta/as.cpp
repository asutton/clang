// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template<typename Out, typename In>
constexpr void copy(Out out, In in) {
  for... (auto x : in.member_variables())
    __extend(out) x;
  for... (auto x : in.member_functions())
    __extend(out) x;
}

struct S { int a, b, c; };

using class foo as copy($S);

constexpr {
  meta::compiler.debug($foo);
}

int main() { }
