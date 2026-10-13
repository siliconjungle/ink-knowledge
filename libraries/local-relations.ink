module ink.knowledge.local_relations;

// A frame is an observation preserved by every step, not a permission to
// reorder writes or events. Each implementation proves the step assumption.
law foldl_frame<A,S,O>(xs:List<A>,initial:S,step:fn(A,S)->S,frame:fn(S)->O) {
 assume unchanged(item:A,state:S):frame(step(item,state))==frame(state);
 frame(foldl(xs,initial,fn(item,acc)=>step(item,acc)))==frame(initial);
 proof by induction xs generalizing(initial) {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==frame(foldl(tail,step(head,initial),fn(item,acc)=>step(item,acc))) by normalize;
   ==frame(step(head,initial)) by ih(initial=step(head,initial));
   ==_ by assumption unchanged(head,initial);
  };
 };
}

// Two evolving representations share the same ordered input. The relation is
// required only on the actual initial states and preserved at each valid step.
law foldl_relates<A,P,L>(xs:List<A>,physical:P,logical:L,
 physical_step:fn(A,P)->P,logical_step:fn(A,L)->L,relate:fn(P,L)->Bool,accept:fn(A)->Bool) {
 assume preserves(item:A,p:P,l:L) requires accept(item),relate(p,l):
  relate(physical_step(item,p),logical_step(item,l))==true;
 choose(relate(physical,logical)&&foldr(xs,true,fn(item,ok)=>accept(item)&&ok),
  relate(foldl(xs,physical,fn(item,acc)=>physical_step(item,acc)),
         foldl(xs,logical,fn(item,acc)=>logical_step(item,acc))),true)==true;
 proof by induction xs generalizing(physical,logical) {
  nil=>cases relate(physical,logical) {true=>normalize;false=>normalize;};
  cons(head,tail)=>cases relate(physical,logical) {
   false=>normalize;
   true=>cases accept(head) {
    false=>normalize;
    true=>cases foldr(tail,true,fn(item,ok)=>accept(item)&&ok) {
     false=>normalize;
     true=>assert relate(physical_step(head,physical),logical_step(head,logical))==true
      by cases relate(physical_step(head,physical),logical_step(head,logical)) {
       true=>normalize;false=>assumption preserves(head,physical,logical);
      } then ih(physical=physical_step(head,physical),logical=logical_step(head,logical));
    };
   };
  };
 };
}

record Independent { total:u32, retained:Bool, }
law foldl_simulates<A,P,L>(xs:List<A>,physical:P,logical:L,
 physical_step:fn(A,P)->P,logical_step:fn(A,L)->L,relate:fn(P,L)->Bool) {
 assume preserves(item:A,p:P,l:L) requires relate(p,l):
  relate(physical_step(item,p),logical_step(item,l))==true;
 choose(relate(physical,logical),
  relate(foldl(xs,physical,fn(item,acc)=>physical_step(item,acc)),
         foldl(xs,logical,fn(item,acc)=>logical_step(item,acc))),true)==true;
 proof by induction xs generalizing(physical,logical) {
  nil=>cases relate(physical,logical) {true=>normalize;false=>normalize;};
  cons(head,tail)=>cases relate(physical,logical) {
   false=>normalize;
   true=>assert relate(physical_step(head,physical),logical_step(head,logical))==true
    by cases relate(physical_step(head,physical),logical_step(head,logical)) {
     true=>normalize;false=>assumption preserves(head,physical,logical);
    } then ih(physical=physical_step(head,physical),logical=logical_step(head,logical));
  };
 };
}
law independent_record_frame(xs:List<u32>,initial:Independent) {
 foldl(xs,initial,fn(item,acc)=>Independent{total:acc.total+item,retained:acc.retained}).retained==initial.retained;
 proof by use foldl_frame<u32,Independent,Bool>(xs,initial,
  fn(item,acc)=>Independent{total:acc.total+item,retained:acc.retained},fn(acc)=>acc.retained);
}
law all_true<A>(xs:List<A>) {
 foldr(xs,true,fn(item,ok)=>true&&ok)==true;
 proof by induction xs;
}
law buffer_list_relation<A>(xs:List<A>,physical:Buffer<A>,logical:List<A>) {
 choose(physical.freeze()==logical,
  foldl(xs,physical,fn(item,acc)=>acc.push(item)).freeze()
   ==foldl(xs,logical,fn(item,acc)=>acc.concat([item])),true)==true;
 proof by use foldl_simulates<A,Buffer<A>,List<A>>(xs,physical,logical,
   fn(item,acc)=>acc.push(item),fn(item,acc)=>acc.concat([item]),fn(p,l)=>p.freeze()==l)
   assuming(normalize);
}
