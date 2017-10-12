// RUN: %clang -std=c++1z -Xclang -freflection %s 

constexpr {
  -> do { } // expected-error{{injecting statements into global scope}}
  -> class C { } // expected-error{{injecting class members into global scope}}
}
