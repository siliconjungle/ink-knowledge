module ink.knowledge.independent_fold_batching;

law map_identity<A>(xs:List<A>) {
 xs.map(fn(x)=>x)==xs;
 proof by induction xs;
}
law map_fusion<A,B,C>(xs:List<A>,f:fn(A)->B,g:fn(B)->C) {
 xs.map(f).map(g)==xs.map(fn(x)=>g(f(x)));
 proof by induction xs;
}

// Each state retains the original left-to-right input order. This law does
// not assume associative arithmetic, commutativity, equal states, or a size.
// The state type can retain immutable per-lane data alongside an accumulator.
law independent_fold_batch<A,S>(xs:List<A>,states:List<S>,step:fn(A,S)->S) {
 states.map(fn(state)=>foldl(xs,state,step))
 ==foldl(xs,states,fn(item,current)=>current.map(fn(state)=>step(item,state)));
 proof by induction xs generalizing(states) {
  nil=>use map_identity<S>(states);
  cons(head,tail)=>calc {
   _==states.map(fn(state)=>step(head,state)).map(fn(state)=>foldl(tail,state,step))
    by symmetry(use map_fusion<S,S,S>(states,fn(state)=>step(head,state),fn(state)=>foldl(tail,state,step)));
   ==foldl(tail,states.map(fn(state)=>step(head,state)),fn(item,current)=>current.map(fn(state)=>step(item,state)))
    by ih(states=states.map(fn(state)=>step(head,state)));
   ==_ by normalize;
  };
 };
}

// Non-associative arithmetic is intentional: each floating lane keeps its
// original sequence of additions and multiplications.
law float_independent_folds(xs:List<f32>,states:List<f32>) {
 states.map(fn(state)=>foldl(xs,state,fn(item,acc)=>(acc+item)*item))
 ==foldl(xs,states,fn(item,current)=>current.map(fn(acc)=>(acc+item)*item));
 proof by use independent_fold_batch<f32,f32>(xs,states,fn(item,acc)=>(acc+item)*item);
}
