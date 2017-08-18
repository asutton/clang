
#include <cppx/meta>
#include <cppx/compiler>

$class test { 
  constexpr {
    for... (auto m : $prototype.member_variables()) {
      -> m;
    }

    for... (auto m : $prototype.member_variables()) {
      -> class {
        typename(m) idexpr("get_", m)() const {
          return idexpr(m);
        }
      }
    }
  } // constexpr

};

test foo {
  int n;
  // char c;
  // float f;
};


int main()
{
  compiler.debug($foo);
}
