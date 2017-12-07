// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>

using namespace cppx;

template <class MetaType>
void make_interface(MetaType& source)
{
  auto target = __fragment class idexpr(source.name()) { };
}
