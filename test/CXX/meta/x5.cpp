// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

using HRESULT = unsigned long;

constexpr void gen_garbage()
{
  auto f1 = __fragment class {
    int a, b, c, d;
    void foobar() { return; }
  };
  __generate f1;
}

// Copy member variables as pubic.
template<typename T>
constexpr void gen_vars(T proto)
{
  for... (auto var : proto.member_variables()) {
    var.make_private();
    __generate var;
  }
};

// Copy member functions as public
template<typename T>
constexpr void gen_fns(T proto)
{
  for...(auto fn : proto.member_functions()) {
    fn.make_public();
    __generate fn;
  }
}

template<typename T>
constexpr void rt_class(T proto) {
  auto impl = __fragment class impl_type {
    constexpr { 
      gen_garbage();
      gen_vars(proto); 
      gen_fns(proto);
    }
  };
  __generate impl;
}

struct Circle_proto {
  int data1, data2 = 12;
  int f(int i, int j) { return i+j; }
  int g(double d) { return (int)d; }
  void h() { return; }
};

struct Circle {
  using prototype = Circle_proto;
  constexpr { rt_class($Circle_proto); }
};

constexpr {
  meta::compiler.debug($Circle);
}



int main() {
}

