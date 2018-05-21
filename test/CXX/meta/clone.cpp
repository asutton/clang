// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

struct proto {
  int n;
  char c;
  int f() { return 1; }
};

struct final1 {
  constexpr {
    for... (auto x : $proto.member_variables()) {
      x.make_static();
      __generate x;
    }

    __generate $proto::f;

  } // constexpr
};

template<typename T>
struct final2 {
  constexpr {
    for... (auto x : $proto.member_variables()) {
      __generate x;
    }
  }
};


int main() { 
  compiler.debug($final1);

  final1 f1;
  (void)final1::n;
  assert(f1.f() == 1);

  final2<int> f2;
  compiler.debug($final2<int>);
}
