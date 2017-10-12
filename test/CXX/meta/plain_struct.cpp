// RUN: %clang -std=c++1z -Xclang -freflection %s 

$class plain_struct : basic_value {
 constexpr {
 for (auto f : plain_struct.functions()) {
 compiler.require(f.is_public() || !f.is_virtual())
 "a plain_struct function must be public and nonvirtual");
 compiler.require(!(f.is_ctor() || f.is_dtor() || f.is_copy() || f.is_move())
 || f.has_default_body())
 "a plain_struct can’t have a user-defined "
  "constructor, destructor, or copy/move");
 }
 bool all_ordered = true, // to compute common comparability
 all_weakly_ordered = true,
 all_partially_ordered = true,
 all_equal = true,
 all_weakly_equal = true;
 for (auto o : plain_struct.variables()) {
 if (!o.has_access()) o.make_public();
 compiler.require(o.is_public(), "plain_struct members must be public");
 all_ordered &= o.type.is(ordered);
 all_weakly_ordered &= o.type.is(weakly_ordered);
 all_partially_ordered &= o.type.is(partially_ordered);
 all_equal &= o.type.is(equal);
 all_weakly_equal &= o.type.is(weakly_equal);
 }
 if (all_ordered) // generate greatest common comparability
 plain_struct = plain_struct.as(ordered);
 else if (all_equal)
 plain_struct = plain_struct.as(equal);
 else if (all_weakly_ordered)
 plain_struct = plain_struct.as(weakly_ordered);
 else if (all_weakly_equal)
 plain_struct = plain_struct.as(weakly_equal);
 else if (all_partially_ordered)
 plain_struct = plain_struct.as(partially_ordered);
 }
};