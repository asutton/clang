
#include <cppx/meta>

template<typename Out, typename In>
constexpr void meta(Out out, In in)
{
  for... (auto x : in.members())
    __extend(out) x;

  __extend(out) class {
    int f() { return 0; }
  };
}

struct(meta) MyMeta
{
  int x;
};



int main()
{
  compiler.debug($MyMeta);
};
