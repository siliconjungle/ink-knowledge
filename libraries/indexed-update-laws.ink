module ink.knowledge.indexed_update_laws;
law repeated_set<A>(xs:List<A>,index:u32,first:A,second:A){
 buffer(buffer(xs).set(index,first).freeze()).set(index,second).freeze()
  == buffer(xs).set(index,second).freeze();
 proof by induction xs generalizing(index){
  nil=>normalize;
  cons(head,tail)=>cases index==0{
   true=>normalize;
   false=>calc{
    _==[head].concat(buffer(buffer(tail).set(index-1,first).freeze()).set(index-1,second).freeze()) by normalize;
     ==[head].concat(buffer(tail).set(index-1,second).freeze()) by congruence(normalize,ih(index=index-1));
     ==_ by normalize;
   };
  };
 };
}
law set_same<A>(xs:List<A>,index:u32,fallback:A){
 buffer(xs).set(index,xs.at_or(index,fallback)).freeze()==xs;
 proof by induction xs generalizing(index){
  nil=>normalize;
  cons(head,tail)=>cases index==0{
   true=>normalize;
   false=>calc{
    _==[head].concat(buffer(tail).set(index-1,tail.at_or(index-1,fallback)).freeze()) by normalize;
     ==[head].concat(tail) by congruence(normalize,ih(index=index-1));
     ==_ by normalize;
   };
  };
 };
}
