
#include <cassert>
#include <iostream>

#include <cpp3k/meta>

namespace meta = cpp3k::meta;

template<typename T>
struct compare_data_members
{
  const T& a;
  const T& b;
  bool& result;
  
  template<meta::reflection_t X>
  void operator()(meta::member_variable<X> member) const
  {
    auto ptr = member.pointer();
    result &= a.*ptr == b.*ptr;
  }

  // As an alternative -- if we had concepts.
  //
  // template<MemberVariable T>
  // void operator()(T member) const;
};

// TODO: This should only be defined when no members are references or 
// mutable. And what about private members? Obviously, we could write a
// very nice constraint for when this should be defined.
//
// I wonder if we can suppress this definition if there's an existing
// user-defined customization. Note that the customization would be 
// more specialized, so no harm, no foul, I suppose.
template<typename T>
bool is_equal(const T& a, const T& b)
{
  bool result = true;
  meta::for_each($T.member_variables(), compare_data_members<T>{a, b, result});
  return result;
}

struct S
{
  int first;
  char second;
};

int main()
{
  S s0 { 0, 1 };
  S s1 { 1, 2 };
  assert(is_equal(s0, s0));
  assert(!is_equal(s0, s1));
}



