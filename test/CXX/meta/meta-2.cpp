// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx;

template <class Out, typename In>
constexpr void test(Out out, In in)
{
  for... (auto f : in.functions()) {
    if (!f.parameters().empty()) {
      auto fn = __fragment class {
        void idexpr(f.name())(__inject(f.parameters())); 
      };
      __extend(out) fn;
    }
    else { 
      auto fn = __fragment class {
        void idexpr(f.name())();
      };
      __extend(out) fn;
    }
  }
}


class(test) Shape {
public:
  int area() const; 
  void scale_by(double factor);
};

constexpr { compiler.debug($Shape); }

int main() { }