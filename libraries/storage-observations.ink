module ink.knowledge.storage_observations;
// Generic observational laws. Implementations must prove the step assumption;
// naming a storage family or observer does not grant that assumption.
law concat_associates<A>(xs:List<A>,ys:List<A>,zs:List<A>){
 xs.concat(ys).concat(zs)==xs.concat(ys.concat(zs));
 proof by induction xs;
}
law concat_empty<A>(xs:List<A>){xs.concat([])==xs;proof by induction xs;}
law foldl_observe_append<A,S>(xs:List<A>,initial:S,step:fn(A,S)->S,observe:fn(S)->List<A>){
 assume preserves(item:A,state:S):observe(step(item,state))==observe(state).concat([item]);
 observe(foldl(xs,initial,fn(item,acc)=>step(item,acc)))==observe(initial).concat(xs);
 proof by induction xs generalizing(initial){
  nil=>symmetry(use concat_empty<A>(observe(initial)));
  cons(head,tail)=>calc{
   _==observe(foldl(tail,step(head,initial),fn(item,acc)=>step(item,acc))) by normalize;
   ==observe(step(head,initial)).concat(tail) by ih(initial=step(head,initial));
   ==observe(initial).concat([head]).concat(tail) by congruence(assumption preserves(head,initial),normalize);
   ==_ by use concat_associates<A>(observe(initial),[head],tail);
  };
 };
}

law buffer_push_append<A>(items:List<A>,item:A){
 buffer(items).push(item).freeze()==items.concat([item]);
 proof by induction items;
}
law list_append_fold<A>(xs:List<A>,initial:List<A>){
 foldl(xs,initial,fn(item,acc)=>acc.concat([item]))==initial.concat(xs);
 proof by use foldl_observe_append<A,List<A>>(xs,initial,fn(item,acc)=>acc.concat([item]),fn(acc)=>acc);
}
law buffer_append_fold<A>(xs:List<A>,initial:Buffer<A>){
 foldl(xs,initial,fn(item,acc)=>acc.push(item)).freeze()==initial.freeze().concat(xs);
 proof by use foldl_observe_append<A,Buffer<A>>(xs,initial,fn(item,acc)=>acc.push(item),fn(acc)=>acc.freeze())
  assuming (use buffer_push_append<A>(__assumed_state.freeze(),__assumed_item));
}
