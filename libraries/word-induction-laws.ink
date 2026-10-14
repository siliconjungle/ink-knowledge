module ink.knowledge.word_induction_laws;
// External proof source. Every use must prove adjacent preservation for its
// actual function; the maximum word is excluded only in the successor premise.
law constant_u32(count:u32,f:fn(u32)->u32){
 assume adjacent(item:u32) requires item<4294967295:
  f(item+1)==f(item);
 f(count)==f(0);
 proof by induction count{
  zero=>normalize;
  succ(previous)=>calc{
   _==f(previous) by assumption adjacent(previous);
    ==_ by ih;
  };
 };
}
law constant_u64(count:u64,f:fn(u64)->u64){
 assume adjacent(item:u64) requires item<18446744073709551615:
  f(item+1)==f(item);
 f(count)==f(0);
 proof by induction count{
  zero=>normalize;
  succ(previous)=>calc{
   _==f(previous) by assumption adjacent(previous);
    ==_ by ih;
  };
 };
}
