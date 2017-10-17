// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

#include <algorithm>
#include <type_traits>

// $class safe_union : final, comparable_value { // no derivation
$class safe_union  {
  constexpr {
    std::size_t size = 1; // first, calculate the required size
    std::size_t align = 1; // and alignment for the data buffer
    for (auto o : $prototype.variables()) {
     size = std::max(size, sizeof(typename(o)));
     align = std::max(align, alignof(typename(o)));

     // FIXME: I don't know what this does.       
     // if (o.storage.has_default()) 
     //    o.make_member();
     
     compiler.require(o.is_member(), "safe_union members must not be static");
     compiler.require(
          std::is_copy_constructible_v<typename(o)> && 
          std::is_copy_assignable_v<typename(o)>,
          "safe_union members must be copy constructible and copy assignable");
    }

    __generate class {
       alignas(align) unsigned char data[size]; // with a data buffer
       int active; // and a discriminant
    };
  }

  safe_union() { active = 0; } // default constructor
  
  void clear() { // cleanup goes here
    switch (active) {
      constexpr {
      for (const auto& o : objects) // destroy the active object
        
        // FIXME: Statement injection not yet implemented.  
        // __generate { case o.num$: o.name$.~(o.type.name$)(); }
      
      }
      active = 0;
    }
  }
  
  ~safe_union() { clear(); } // destructor just invokes cleanup

#if 0

  safe_union(const safe_union& that) // copy construction
  : active{that.active}
  {
  switch (that.active) {
  constexpr {
  for (auto o : objects) // just copy the active member
  -> { case o.num$: o.name$() = that.(o.name)$(); }
  } // via its accessor, defined next below
  }
  }
  safe_union& operator=(const safe_union& that) { // copy assignment
  clear(); // to keep the code simple for now,
  active = that.active; // destroy-and-construct even if the
  switch (that.active) { // same member is active
  constexpr {
  for (auto o : objects) // just copy the active member
  -> { case o.num$: o.name$() = that.(o.name)$(); }
  } // via its accessor, defined next below
  }
  }
  constexpr {
  for (auto o : objects) -> { // for each original member
  auto o.name$() { // generate an accessor function
  assert (active==o.num); // assert that the member is active
  return (o.type$&)data;
  } // and cast data to the appropriate type&
  void operator=(o.type$ value){ // generate a value-set function
  if (active==o.num)
  o.name$() = value; // if the member is active, just set it
  else {
  clear(); // otherwise, clean up the active member
  active = o.num; // and construct a new one
  try { new (&data[0]) o.type.name$(value); }
  catch { active = 0; } // failure to construct implies empty
  }
  }
  bool is_(o.name)$() { // generate an is-active query function
  return (active==o.num);
  }
  }
  }
  bool operator==(const safe_union& that) const {
  // (we’ll get != from ‘comparable_value’)
  if (active != that.active) // different active members => not equal
  return false;
  if (active == 0) // both empty => equal
  return true;
  switch (that.active) {
  constexpr {
  for (auto o : objects) // else just compare the active member
  -> { case o.num$: return o.name$() == that.(o.name)$(); }
  }
  }
  }
  bool is_empty() { return active == 0; }
#endif
};

int main() {

}
