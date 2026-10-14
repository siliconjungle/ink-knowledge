module ink.knowledge.fold_representations;
// A physical carrier need not equal its logical observation. Every step must
// preserve that observation for ALL physical states, including unused bits.
law foldl_observation<A,L,P>(xs:List<A>,physical:P,
 observe:fn(P)->L,logical_step:fn(A,L)->L,physical_step:fn(A,P)->P) {
 assume advances(item:A,state:P):
  observe(physical_step(item,state))==logical_step(item,observe(state));
 observe(foldl(xs,physical,physical_step))
  ==foldl(xs,observe(physical),logical_step);
 proof by induction xs generalizing(physical) {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==observe(foldl(tail,physical_step(head,physical),physical_step)) by normalize;
   ==foldl(tail,observe(physical_step(head,physical)),logical_step)
    by ih(physical=physical_step(head,physical));
   ==foldl(tail,logical_step(head,observe(physical)),logical_step)
    by congruence(normalize,assumption advances(head,physical),normalize);
   ==_ by normalize;
  };
 };
}

// An exact encoded alternative is another instance of the same step law.
law foldl_encoding<A,L,P>(xs:List<A>,logical:L,
 encode:fn(L)->P,logical_step:fn(A,L)->L,physical_step:fn(A,P)->P) {
 assume advances(item:A,state:L):
  encode(logical_step(item,state))==physical_step(item,encode(state));
 encode(foldl(xs,logical,logical_step))
  ==foldl(xs,encode(logical),physical_step);
 proof by use foldl_observation<A,P,L>(xs,logical,encode,physical_step,logical_step)
  assuming(assumption advances(__assumed_item,__assumed_state));
}
