module ink.knowledge.ordered_slice_laws;
law slice_reconstruction<A>(xs:List<A>,n:u32){
 xs.take(n).concat(xs.drop(n))==xs;
 proof by induction xs generalizing(n){
  nil=>normalize;
  cons(head,tail)=>cases n==0 {
   true=>normalize;
   false=>calc {
    _==[head].concat(tail.take(n-1).concat(tail.drop(n-1))) by normalize;
     ==[head].concat(tail) by congruence(normalize,ih(n=n-1));
     ==_ by normalize;
   };
  };
 };
}
law foldr_append<A,S>(xs:List<A>,ys:List<A>,seed:S,step:fn(A,S)->S){
 foldr(xs.concat(ys),seed,step)==foldr(xs,foldr(ys,seed,step),step);
 proof by induction xs {nil=>normalize;cons(head,tail)=>normalize;};
}
law foldr_split<A,S>(xs:List<A>,n:u32,seed:S,step:fn(A,S)->S){
 foldr(xs,seed,step)==foldr(xs.take(n),foldr(xs.drop(n),seed,step),step);
 proof by calc {
  _==foldr(xs.take(n).concat(xs.drop(n)),seed,step) by congruence(symmetry(use slice_reconstruction<A>(xs,n)),normalize,normalize);
   ==_ by use foldr_append<A,S>(xs.take(n),xs.drop(n),seed,step);
 };
}
