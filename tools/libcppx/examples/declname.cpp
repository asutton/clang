#include <iostream>

#include <cppx/meta>


int f() { return 42; }

int main()
{
  auto fn = $f;
  std::cout << declname(fn)() << '\n';

  int loc = 12;
  auto var = $loc;
  std::cout << declname(var) << '\n';
}

