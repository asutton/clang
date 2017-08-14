// RUN: echo

#include <cppx/meta>
#include <cppx/compiler>

using namespace cppx::meta;

$class interface {
  virtual ~interface() noexcept = default;

  // Check for invalid members.
  constexpr {
    compiler.require($prototype.member_variables().empty(),
      "interfaces may not contain data members");
    
    for... (auto f : $prototype.member_functions()) {
      compiler.require(f.is_public(), 
        "interface functions must be public");

      compiler.require(!f.is_copy() && !f.is_move(),
        "interfaces may not copy or move; consider a virtual clone()");
    }
  } // end constexpr
    
  // Transform members.
  constexpr {
    for... (auto f : $prototype.member_functions()) {
      f.make_pure_virtual();
      -> f;
    }
  } // end constexpr;
} 


interface Shape {
  int area() const;
  void scale_by(double factor);
  
  // ...
  // int x; // error: interfaces may not contain data members
};

int main() {
  compiler.debug($Shape);
}
