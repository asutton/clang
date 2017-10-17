// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

$class test { 
  constexpr {
    for... (auto m : $prototype.member_variables()) {
      __generate m;
    }

    for... (auto m : $prototype.member_variables()) {
      __generate class {
        typename(m) idexpr("get_", m)() const {
          return idexpr(m);
        }
      };
    }
  } // constexpr

};

test foo {
  int n;
  char c;
  float f;
};


int main()
{
  compiler.debug($foo);
}
