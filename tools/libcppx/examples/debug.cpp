#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

$class interface {
  virtual ~interface() { }
  
  constexpr {
    for... (auto fn : $interface.member_functions())
      fn.make_pure_virtual();
  }
}

interface IFoo {
  void foo();
};

int main() {
  compiler.debug($IFoo);
}
