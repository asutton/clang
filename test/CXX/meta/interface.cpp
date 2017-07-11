// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

$class interface {
  // Check for invalid members.
  constexpr {
    // NOTE: The first reference of $interface.member_variables() instantiates
    // the list of member variables that will be available for *all* subsequent
    // queries. This is the result of an unexpected interaction with our 
    // approach to reflection and our approach to metaclass application. See 
    // the note on the destructor below.
    compiler.require($interface.member_variables().empty(),
      "interfaces may not contain data members");
    
    for... (auto f : $interface.member_functions()) {
      compiler.require(f.is_public(), 
        "interface functions must be public");

      compiler.require(!f.is_copy() && !f.is_move(),
        "interfaces may not copy or move; consider a virtual clone()");
    }
  }
    
  // Transform members later.
  //
  // NOTE: These changes are not observable within this metaprogram.
  constexpr {
    for... (auto f : $interface.member_functions()) {
      if (!f.has_access()) f.make_public();
      if (!f.is_virtual()) f.make_pure_virtual();
    }
  }

  // Add new members here.
  //
  // NOTE: Add members last. This guarantees that injected members cannot be
  // observed or modified during metaclass application.
  ~interface() noexcept = default;
  
} // end constexpr;


interface Shape {
  int area() const;
  void scale_by(double factor);
  // ...
};

int main() {
  compiler.debug($Shape);
}
