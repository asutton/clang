
#include <cppx/meta>
#include <cppx/compiler>

constexpr auto f1() {
  return __fragment class {
    char c;
    int n;
  };
}

template<typename T>
constexpr auto f2() {
  return __fragment class {
    T a;
    T b;
  };
}

int main() {
  constexpr auto x1 = f1(); 
  compiler.debug(x1);

  constexpr auto x2 = f2<int>();
  compiler.debug(x2);
}

