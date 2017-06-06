// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

$class interface
{
  virtual ~interface() = default;

  constexpr {
    if (!$interface.member_variables().empty())
      compiler.error("interface cannot have member variables");
    for... (auto x : $interface.member_functions())
      x.make_pure_virtual();
  }
}

interface ifoo
{
  void foo();
};


int main() {
  compiler.debug($ifoo);
}