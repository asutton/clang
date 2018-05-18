#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

struct blah { };

constexpr auto members() {
  auto f1 = __fragment struct C {
    int n = 17;
    int f() { return n + this->m; }
    int g(int k) { return n + k; }

    struct inner : blah { 
      int g(int k) { return 42 + k; } 
    };

    typedef int T1;
    using T2 = int;

    enum E { A, B = 42 };
  };
  return f1;
}

class X {
  int m = 42;
public:
  constexpr {
    __generate members();
  }
};

constexpr {
  meta::compiler.debug($X);
}

int main() {
  // X x;
  // assert(x.n == 17);
  // assert(x.f() == 17 + 42);
  // X::T1 n1 = 4;
  // X::T2 n2 = 5;
}

