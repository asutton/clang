// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

struct orig
{
  int a = 42;
  int f() { return a; }
};


class X1 {
  constexpr {
    for... (auto var : $orig.member_variables()) {
      __generate var;      
    }

    for... (auto fn : $orig.member_functions()) {
      __generate fn;      
    }
  }
};

struct X2 {
  int a = 57;
  constexpr {
    for... (auto fn : $orig.member_functions()) {
      __generate fn;      
    }
  }
};

constexpr {
  meta::compiler.debug($X1);
  meta::compiler.debug($X2);
}

int main() {
  X1 x1;
  assert(x1.a == 42);
  assert(x1.f() == 42);

  X2 x2;
  assert(x2.a == 57);
  assert(x2.f() == 57);
}

