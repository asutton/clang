// RUN: %clang -std=c++1z -Xclang -freflection %s 

$class final {
  constexpr {
    $final.make_final();
  }
}

int main() {
  
}