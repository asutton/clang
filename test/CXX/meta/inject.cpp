// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

constexpr auto init()
{
  return __fragment struct C {
    int a, b, c;
    void f() { }
  };
}

struct C1 {
  constexpr { __generate init(); }
};

template<typename T>
constexpr auto fill(T target)
{
  __extend (target) class {
    int x, y, z;
  };
}

struct C2 {
  constexpr { fill($C2); }
};

namespace proto {
  struct IComparable {
    bool EqualTo(IComparable*);
  };
}

template<typename T, typename U>
constexpr void make_interface(T target, U source)
{
  __extend (target) class C {
    virtual ~C() = default;
  };
}

struct IComparable {
  constexpr { make_interface($IComparable, $proto::IComparable); }
};

int main() { 
  C1 c1; c1.f();
  compiler.debug($C1);
  compiler.debug($C2);
  compiler.debug($IComparable);
}
