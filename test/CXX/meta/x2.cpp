#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template<typename T>
constexpr auto members() {
  auto f1 = __fragment struct C {
    int n = 17;
    int f() { return n + this->m; }    
    T g1(T* ptr) { return *ptr + n; }
    void g2() { auto x = T(); }
  };
  return f1;
}

class X {
  int m = 42;
  constexpr {
    __generate members<int>();
  }
};

constexpr {
  meta::compiler.debug($X);
}

int main() {
  X x;
  assert(x.n == 17);
  assert(x.f() == 17 + 42);
  assert(sizeof(x.g1(&x.n)) == sizeof(int));
  x.g2();
}