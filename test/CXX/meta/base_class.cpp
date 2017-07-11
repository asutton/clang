$class base_class {
  constexpr {
    for (auto f : $base_class.functions()) {
      if (f.is_dtor() && !(f.is_public() && f.is_virtual()) && !(f.is_protected() && !f.is_virtual()))
        compiler.error("base class destructors must be public and "
                       "virtual, or protected and nonvirtual");
      
      if (f.is_copy() || f.is_move())
        compiler.error("base classes may not copy or move; "
                       " consider a virtual clone() instead");
      }
      
      for (auto b : $base_class.base_classes())
        if (b.is(interface) && !b.has_access())
          f.make_public();
      
      if (!$base_class.variables().empty())
        compiler.error("pure base classes may not contain data");
  }
};
