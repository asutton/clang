#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

void blah(int a, char b) { }

template<typename T>
constexpr void f2(T parm) {
  __generate struct {
    void foo(int n, __inject(parm.parameters()) args, int m) {
      // FIXME: blah produces a lookup error if its declaration does not
      // occur before its use here. I'm not sure if that should be expected
      // or not.
      blah(args...);
    }
  };
}

struct S {
  constexpr {
    f2($blah);
  }
};

constexpr {
  meta::compiler.debug($S);
}

int main() {
  S test;
  test.foo(0, 1, 2, 3);
}
