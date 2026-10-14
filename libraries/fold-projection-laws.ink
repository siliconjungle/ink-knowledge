module ink.knowledge.fold_projection_laws;
// Pure loop-state projection requires a checked simulation for every step.
law fold_projection<A,S,R>(xs:List<A>,initial:S,project:fn(S)->R,step:fn(A,S)->S,reduced:fn(A,R)->R){
 assume simulation(item:A,state:S): project(step(item,state))==reduced(item,project(state));
 project(foldl(xs,initial,step))==foldl(xs,project(initial),reduced);
 proof by induction xs generalizing(initial){
  nil=>normalize;
  cons(head,tail)=>calc{
   _==foldl(tail,project(step(head,initial)),reduced) by ih(initial=step(head,initial));
    ==foldl(tail,reduced(head,project(initial)),reduced) by congruence(normalize,assumption simulation(head,initial),normalize);
    ==_ by normalize;
  };
 };
}
