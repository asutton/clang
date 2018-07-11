// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template<typename T>
constexpr void basic_value(T proto) {
  __generate __fragment struct X {
    X() = default;
    X(const X& that) = default;
    X(X&& that) = default;
    X& operator=(const X& that) = default;
    X& operator=(X&& that) = default;
  };

  for... (auto v : proto.variables()) {
    if (v.has_default_access()) 
      v.make_private();
    __generate v;
  }

  for... (auto f : proto.functions()) {
    meta::compiler.require(!f.is_protected(), "a value type may not have a protected function");
    meta::compiler.require(!f.is_virtual(), "a value type may not have a virtual function");
    meta::compiler.require(!f.is_destructor() || f.is_public(), "a value destructor must be public");

    if (f.has_default_access())
      f.make_public();
  
    __generate f;
  }
};


template<typename T>
constexpr void value(T proto) {
  basic_value(proto); // value is-a basic_value
};


class(value) Point {
  int x = 0, y = 0;
  Point(int xx, int yy) : x{xx}, y{yy} { }
};

constexpr {
  meta::compiler.debug($Point);
}

int main() {
  Point p1(50,100);
  // Point p2;

  // p2 = get_some_point();
  // p2.x = 42;

}
