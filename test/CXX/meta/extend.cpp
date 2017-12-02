// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

constexpr auto init()
{
  return __fragment class my_class {
  };
}

template<typename T>
constexpr void add_members(T& tgt)
{
  __extend (tgt) class {
    int m, n;
    void f() { return n; }
  };
}


constexpr {
  auto c = init();
  add_members(c);
  compiler.debug(c);
}

int main() { 
}
