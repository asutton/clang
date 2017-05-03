#include <iostream>

#include <cppx/meta>

struct S
{
  int first = 3;
  char second = 'a';
};

int main()
{
  typename($S) x; // equivalent to 'S x;'
  std::cout << $x.type().name() << '\n';  

  auto T = $x.type();
  typename(T) y; // also equivalent to 'S x'.
  std::cout << $y.type().name() << '\n';  
}

