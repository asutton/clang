#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template<typename T>
constexpr auto members() {
  auto x = $T;
  return __fragment struct {
    static constexpr auto rt = x;
  };
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
}

