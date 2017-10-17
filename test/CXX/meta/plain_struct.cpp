// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

// FIXME: These are probably mean to be metaclasses.
enum {
  ordered,
  weakly_ordered,
  partially_ordered,
  equal,
  weakly_equal,
};

// $class plain_struct : basic_value {

$class plain_struct  {
  constexpr {
    for (auto f : $prototype.functions()) {
      compiler.require(
          f.is_public() || !f.is_virtual(),
          "a plain_struct function must be public and nonvirtual");
      compiler.require(
          !(f.is_ctor() || f.is_dtor() || f.is_copy() || f.is_move()) || f.is_defaulted(),
          "a plain_struct can’t have a user-defined constructor, destructor, or copy/move");
    }

    bool all_ordered = true, // to compute common comparability
         all_weakly_ordered = true,
         all_partially_ordered = true,
         all_equal = true,
         all_weakly_equal = true;
    
    for (auto o : $prototype.variables()) {
      if (!o.has_access()) o.make_public();
        compiler.require(o.is_public(), "plain_struct members must be public");
      
      // FIXME: We don't have 'is'.
      all_ordered &= o.type.is(ordered);
      all_weakly_ordered &= o.type.is(weakly_ordered);
      all_partially_ordered &= o.type.is(partially_ordered);
      all_equal &= o.type.is(equal);
      all_weakly_equal &= o.type.is(weakly_equal);
    }
    
    // FIXME: We don't have 'as'.
    //
    // FIXME: __genrate is probably not what you want this to do for a
    // metaclass. But, this makes the example compile, even though it will
    // fail badly when applied.
    if (all_ordered) // generate greatest common comparability
      __generate $prototype.as(ordered);
    else if (all_equal)
      __generate $prototype.as(equal);
    else if (all_weakly_ordered)
      __generate $prototype.as(weakly_ordered);
    else if (all_weakly_equal)
      __generate $prototype.as(weakly_equal);
    else if (all_partially_ordered)
      __generate $prototype.as(partially_ordered);
  }
};

int main() {

}
