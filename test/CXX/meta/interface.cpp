// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

$class interface {
  ~interface() noexcept = default;
  
  // Check for invalid members.
  constexpr {
    compiler.require($interface.member_variables().empty(),
      "interfaces may not contain data members");
    
    for... (auto f : $interface.member_functions()) {
      compiler.require(f.is_public(), 
        "interface functions must be public");

      compiler.require(!f.is_copy() && !f.is_move(),
        "interfaces may not copy or move; consider a virtual clone()");
    }
  } // end constexpr
    
  // Transform members.
  constexpr {
    for... (auto f : $interface.member_functions()) {
      if (!f.has_access()) f.make_public();
      if (!f.is_virtual()) f.make_pure_virtual();
    }
  }
} // end constexpr;


interface Shape {
  int area() const;
  void scale_by(double factor);
  // ...
};

int main() {
  compiler.debug($Shape);
}
