module ink.knowledge.sequence_laws;
// Reusable library mathematics. Assumptions stay parametric until a concrete
// instance discharges them; neither external citations nor tests can do that.
law project_append<A,B>(xs:List<A>,ys:List<A>,visible:fn(A)->Bool,project:fn(A)->B) {
 xs.concat(ys).filter(visible).map(project)
  == xs.filter(visible).map(project).concat(ys.filter(visible).map(project));
 proof by induction xs {
  nil => normalize;
  cons(h,t) => cases visible(h) {true => normalize;false => normalize;};
 };
}
law decode_history<P,L,E>(xs:List<E>,p:P,decode:fn(P)->L,
 physical:fn(P,E)->P,logical:fn(L,E)->L) {
 assume step_commutes(state:P,event:E): decode(physical(state,event)) == logical(decode(state),event);
 decode(foldl(xs,p,fn(event,state)=>physical(state,event)))
  == foldl(xs,decode(p),fn(event,state)=>logical(state,event));
 proof by induction xs generalizing (p) {
  nil => normalize;
  cons(h,t) => calc {
   _ == decode(foldl(t,physical(p,h),fn(event,state)=>physical(state,event))) by normalize;
     == foldl(t,decode(physical(p,h)),fn(event,state)=>logical(state,event)) by ih(p=physical(p,h));
     == foldl(t,logical(decode(p),h),fn(event,state)=>logical(state,event))
        by congruence(normalize,assumption step_commutes(p,h),normalize);
     == _ by normalize;
  };
 };
}
law map_append<T,U>(xs:List<T>,ys:List<T>,project:fn(T)->U) {
 xs.concat(ys).map(project) == xs.map(project).concat(ys.map(project));
 proof by induction xs;
}
law project_buffer_push<T,U>(b:Buffer<T>,x:T,project:fn(T)->U) {
 b.push(x).freeze().map(project) == b.freeze().map(project).concat([project(x)]);
 proof by calc {
  _ == b.freeze().concat([x]).map(project) by normalize;
    == b.freeze().map(project).concat([x].map(project)) by use map_append<T,U>(b.freeze(),[x],project);
    == _ by normalize;
 };
}
law split_reconstruction<T>(xs:List<T>,at:u32) {
 xs.take(at).concat(xs.drop(at)) == xs;
 proof by induction xs generalizing (at) {
  nil => normalize;
  cons(h,t) => cases at==0 {
   true => normalize;
   false => calc {
    _ == [h].concat(t.take(at-1).concat(t.drop(at-1))) by normalize;
      == [h].concat(t) by congruence(normalize,ih(at=at-1));
      == _ by normalize;
   };
  };
 };
}
