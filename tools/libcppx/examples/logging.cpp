
#include <iostream>
#include <string>

#include <cpp3k/meta>

std::ostream& log()
{
  return std::clog;
}


template <typename T>
T minimum(const T& a, const T& b)
{
  log() << "minimum<" << $T.qualified_name() << ">(" << a << ", " << b << ") = ";
  T result = a < b ? a : b;
  log() << result << std::endl;
  return result;
}

int main()
{
  minimum(0, 1);
  minimum(3.14, 2.78);

  std::string a = "abc", 
              b = "def";
  minimum(a, b);
}
