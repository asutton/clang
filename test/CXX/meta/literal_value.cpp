// RUN: %clang -std=c++1z -Xclang -freflection %s 

#include <cppx/meta>
#include <cppx/compiler>

#if 0

There are a couple of interesting things here. Ideally, we'd like to synthesize
a regular or value class, and then modify the resulting members to make them
constexpr. This doesn't work with today's example because the reflection model
doesn't guarantee that we can see injected members. This doesn't work with
the copy-based approach because we can't observe the final class while it is
under construction.

However... 

$class basic_value { 
  // inject members
}

$class literal_value : basic_value {
  
}

If changes from base metaclasses are visible before the application of the
deriving class, then this could be made to work. We could do this by introducing 
intermediaries at each point. So, in applying literal_value we:

1. First apply basic_value, producing a new class C1.
2. Apply literal_value to C1 to create the scratch class C2.
3. Apply C2 to create the final class.

Or, we move back to modify-in-place.

#endif

using namespace cppx::meta;

$class literal_value {
  // Check members
  constexpr {
    for... (auto f : $literal_value.member_functions()) {
      if constexpr (f.is_destructor())
        compiler.debug(f);
      
      compiler.require(!f.is_virtual(),   
                        "a value type may not have a virtual function");
      compiler.require(!f.is_protected(), 
                       "a value type may not have a protected function");
      compiler.require(!f.is_destructor() || f.is_public(), 
                       "a literal destructor must be public");

      // NOTE: You must use 'if constexpr' and not just 'if'. It seems that
      // there is a bug causing the requirement to be evaluated regardless of 
      // the condition (it's being evaluated at the point of translation).
      if constexpr (f.is_destructor())
        compiler.require(f.is_defaulted(), 
                         "an explicit destructor of a literal types must be "
                         "defaulted");
    }
  } // end metaprogram

  // Transform members
  constexpr {
    access_kind mode = default_access;
    for... (auto m : $literal_value.member_functions()) {
      if (mode == default_access) {
        if constexpr (m.is_member_variable()) {
          m.make_private();
        }
        
        if constexpr (m.is_member_function()) {
          m.make_public();
          m.make_constexpr();
        }
        
        if constexpr (m.is_access_specifier())
          mode = m.access();
      }
    }
  } // end metaprogram

  // Inject defaults
  constexpr literal_value() = default;
  constexpr literal_value(const literal_value& that) = default;
  constexpr literal_value(literal_value&& that) = default;
  constexpr literal_value& operator=(const literal_value& that) = default;
  constexpr literal_value& operator=(literal_value&& that) = default;
};


literal_value foo {
public:
  // NOTE: These are explicitly public.
  int a = 5;
  int b = 3;

  // NOTE: This will be made constexpr!
  foo(int a, int b) : a(a), b(b) { }
  
  // NOTE: So will this!
  int f() { return a + b; }
};

constexpr foo fn() {
  foo x{1, 2};
  foo y;
  return foo{x.a + y.a, x.b + y.b};
  return y;
}

constexpr foo f1{6, 5};

// static_assert(fn() == f1);


int main() {
  compiler.debug($foo);
}