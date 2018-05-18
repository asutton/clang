#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;


// Copy member variables as pubic.
template<typename T>
constexpr void gen_vars(T proto)
{
  for... (auto var : proto.member_variables())
    __generate var;
};

// Copy member functions as public
template<typename T>
constexpr void gen_fns(T proto)
{
  for...(auto fn : proto.member_functions())
    __generate fn;
}

template<typename T>
constexpr void duplicate(T proto)
{
  gen_fns(proto);
  gen_vars(proto);
}

struct S { int a, b, c; };

using struct NewType as duplicate($S);

constexpr {
  meta::compiler.debug($NewType);
}

int main() { 
  NewType n;
  (void)n.a;
}
