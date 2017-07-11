$class bitfield : final, comparable_value { // no derivation
 constexpr {
 auto objects = bitfield.variables(); // take a copy of the class’s objects
 size_t size = 0; // first, calculate the required size
 for (auto o : objects) {
 size += (o.bit_length == default ? o.type.size*CHAR_BITS : o.bit_length;
 if (!o.has_storage()) o.make_member();
 compiler.require(o.is_member(), "bitfield members must not be static");
 compiler.require(is_trivially_copyable_v<o.T>,
   "bitfield members must be trivially copyable");
 compiler.require(!o.name.empty() || o.T == $void,
 "unnamed bitfield members must have type void");
 compiler.require(o.type != $void || o.name.empty(),
 "void bitfield members must have an empty name");
 if (o.type != $void) -> { // generate accessors for non-empty members
 o.T$ o.name$ () { return /*bits of this member cast to T*/; }
 set_(o.name)$(const o.T$& val) { /*bits of this value*/ = val; }
 }
 }
 }
 $bitfield.variables().clear(); // now replace the previous instance vars
 byte data[ (size/CHAR_BITS) + 1 ]; // now allocate that much storage
 bitfield() { // default ctor inits each non-pad member
 constexpr {
 for (const auto& o : objects)
 if (o.type != $void)
 -> { new (&data[0]) o.type.name$(); };
 }
 }
 ~bitfield() { // cleanup goes here
 constexpr {
 for (auto o : objects)
 if (o.type != $void)
 -> { o.name$.~(o.type.name$)(); }
 }
 }
 bitfield(const bitfield& that) : bitfield() { // copy constructor
 *this = that; // just delegate to default ctor + copy =
 } // you could also directly init each member by generating a mem-init-list
 bitfield& operator=(const bitfield& that) { // copy assignment operator
 constexpr {
 for (auto o : objects) // copy each non-pad member
 if (o.type != $void) // via its accessor
 -> { case o.num$: set_(o.name$)() = that.(o.name)$(); }
 }
 bool operator==(const bitfield& that) const {
 constexpr { // (we’ll get != from ‘comparable_value’)
 for (auto o : objects) // just compare each member
 -> { if (o.name$() != that.(o.name)$()) return false; }
 return true;
 }
 }
 };
 