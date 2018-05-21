// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template<typename T>
constexpr void rt_interface(T proto)
{
  for... (auto fn : proto.member_functions()) {
    fn.make_pure_virtual();
    __generate fn;
  }
}

class(rt_interface) Circle {
  int data1, data2;
  int f(int i, int j) { return i+j; }
  int g(double d) { return (int)d; }
  void h() { return; }
};

constexpr {
  meta::compiler.debug($Circle);
}

int main() { 
}
