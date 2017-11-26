// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

struct proto {
  int n;
  char c;
  int f1() { return 1; }
};

struct final {
  constexpr {
    for... (auto x : $proto.member_variables()) {
      x.make_static();
      __generate x;
    }

    __generate $proto::f1;

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
  compiler.debug($final);

  final f;
  (void)final::n;
  assert(f.f1() == 1);

  final2<int> f2;
  compiler.debug($final2<int>);
}
