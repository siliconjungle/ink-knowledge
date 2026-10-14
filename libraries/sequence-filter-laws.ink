module ink.knowledge.sequence_filter_laws;
law foldl_filter<A,S>(xs:List<A>,initial:S,p:fn(A)->Bool,step:fn(A,S)->S){
 foldl(xs.filter(p),initial,fn(item,acc)=>step(item,acc))
 ==foldl(xs,initial,fn(item,acc)=>choose(p(item),step(item,acc),acc));
 proof by induction xs generalizing(initial){
  nil=>normalize;
  cons(head,tail)=>cases p(head){true=>ih(initial=step(head,initial));false=>ih(initial=initial);};
 };
}
