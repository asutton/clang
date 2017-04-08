
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
  log() << "function: min<" << $T.qualified_name() << ">(" 
        << $a.name() << ":" << $a.type().name() << ", "
        << $b.name() << ":" << $b.type().name() << ")\n";
  T r = a < b ? a : b;
  log() << $r.name() << ": "<< $r.type().name() << " = " << r << '\n';
  return r;
}

int main()
{
  minimum(0, 1);
  minimum(3.14, 2.78);

  std::string a = "abc", 
              b = "def";
  minimum(a, b);
}
