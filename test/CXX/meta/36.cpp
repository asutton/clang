// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <stddef.h>

#include <cppx/meta>
#include <cppx/compiler>

#include <cassert>

template <typename T>
void func() {
  compiler.debug($T);
}

int
main() {
  auto f = 4;
  
  using T1 = std::decay<decltype(f)>::type;
  compiler.debug($T1);

  typedef std::decay<decltype(f)>::type* T2;
  compiler.debug($T2);

  auto x = 5u;
  compiler.debug($x.type());

  func<void>();
}
