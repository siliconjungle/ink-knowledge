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

// Preservation through a left fold is conditional on every input and the
// initial state. The step relation is proved by each concrete implementation.
law foldl_preserves<A,S>(xs:List<A>,initial:S,step:fn(A,S)->S,valid:fn(S)->Bool,accept:fn(A)->Bool){
 assume preserves(item:A,state:S) requires accept(item),valid(state):valid(step(item,state))==true;
 choose(valid(initial)&&foldr(xs,true,fn(item,ok)=>accept(item)&&ok),
        valid(foldl(xs,initial,fn(item,acc)=>step(item,acc))),true)==true;
 proof by induction xs generalizing(initial){
  nil=>cases valid(initial){true=>normalize;false=>normalize;};
  cons(head,tail)=>cases valid(initial){
   false=>normalize;
   true=>cases accept(head){
    false=>normalize;
    true=>cases foldr(tail,true,fn(item,ok)=>accept(item)&&ok){
     false=>normalize;
     true=>assert valid(step(head,initial))==true by cases valid(step(head,initial)){true=>normalize;false=>assumption preserves(head,initial);} then ih(initial=step(head,initial));
    };
   };
  };
 };
}

law all_concat<A>(xs:List<A>,ys:List<A>,accept:fn(A)->Bool){
 foldr(xs.concat(ys),true,fn(item,ok)=>accept(item)&&ok)
 ==(foldr(xs,true,fn(item,ok)=>accept(item)&&ok)&&foldr(ys,true,fn(item,ok)=>accept(item)&&ok));
 proof by induction xs {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==accept(head)&&(foldr(tail,true,fn(item,ok)=>accept(item)&&ok)&&foldr(ys,true,fn(item,ok)=>accept(item)&&ok)) by normalize;
   ==_ by cases accept(head){false=>normalize;true=>normalize;};
  };
 };
}
law buffer_all_push<A>(owner:Buffer<A>,item:A,accept:fn(A)->Bool){
 foldr(owner.push(item).freeze(),true,fn(value,ok)=>accept(value)&&ok)
 ==(foldr(owner.freeze(),true,fn(value,ok)=>accept(value)&&ok)&&accept(item));
 proof by calc {
  _==foldr(owner.freeze().concat([item]),true,fn(value,ok)=>accept(value)&&ok)
   by congruence(use buffer_push_append<A>(owner.freeze(),item),normalize,normalize);
  ==foldr(owner.freeze(),true,fn(value,ok)=>accept(value)&&ok)&&foldr([item],true,fn(value,ok)=>accept(value)&&ok)
   by use all_concat<A>(owner.freeze(),[item],accept);
  ==_ by normalize;
 };
}
law buffer_fold_preserves<A>(xs:List<A>,initial:Buffer<A>,accept:fn(A)->Bool){
 choose(foldr(initial.freeze(),true,fn(item,ok)=>accept(item)&&ok)&&foldr(xs,true,fn(item,ok)=>accept(item)&&ok),
        foldr(foldl(xs,initial,fn(item,acc)=>acc.push(item)).freeze(),true,fn(item,ok)=>accept(item)&&ok),true)==true;
 proof by use foldl_preserves<A,Buffer<A>>(xs,initial,fn(item,acc)=>acc.push(item),
   fn(owner)=>foldr(owner.freeze(),true,fn(item,ok)=>accept(item)&&ok),accept)
  assuming (use buffer_all_push<A>(__assumed_state,__assumed_item,accept));
}
