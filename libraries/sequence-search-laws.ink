module ink.knowledge.sequence_search_laws;

// Ordered existence search can stop after its first witness. The predicate is
// arbitrary pure total source knowledge; no collection or function name grants
// applicability. Each concrete instantiation replays this ordinary induction.
law foldr_any<A>(xs:List<A>,p:fn(A)->Bool){
 foldr(xs,false,fn(item,found)=>p(item)||found)
 ==fold_until(xs,false,fn(item,found)=>p(item),fn(item,found)=>p(item)||found);
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>cases p(head){true=>normalize;false=>ih;};
 };
}
