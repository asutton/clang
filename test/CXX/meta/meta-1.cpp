// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using HRESULT = int; 

template <class Out, typename In>
constexpr void just_echo_func_names(Out out, In in)
{
  for... (auto f : in.functions()) {
    auto fn = __fragment class {
      void idexpr(f.name())();
    };
    __extend(out) fn;
  }
}

class(just_echo_func_names) Shape {
public:
  int area() const;
  void scale_by(double factor);
};

constexpr { 
  compiler.debug($Shape); 
}

int main() { }
