module ink.knowledge.boolean_folds;
// Predicate-independent accumulation equivalence, proved for arbitrary lists.
// This is reusable proof data; it does not grant an unchecked loop rewrite.
law foldl_any<A>(xs:List<A>,initial:Bool,predicate:fn(A)->Bool) {
 foldl(xs,initial,fn(item,found)=>found||predicate(item))==(foldr(xs,false,fn(item,found)=>predicate(item)||found)||initial);
 proof by induction xs generalizing(initial) {
  nil=>cases initial {true=>normalize;false=>normalize;};
  cons(head,tail)=>calc {
   _==foldl(tail,initial||predicate(head),fn(item,found)=>found||predicate(item)) by normalize;
   ==(foldr(tail,false,fn(item,found)=>predicate(item)||found)||(initial||predicate(head))) by ih(initial=initial||predicate(head));
   ==_ by cases initial {
    true=>cases predicate(head) {true=>cases foldr(tail,false,fn(item,found)=>predicate(item)||found) {true=>normalize;false=>normalize;};false=>cases foldr(tail,false,fn(item,found)=>predicate(item)||found) {true=>normalize;false=>normalize;};};
    false=>cases predicate(head) {true=>cases foldr(tail,false,fn(item,found)=>predicate(item)||found) {true=>normalize;false=>normalize;};false=>cases foldr(tail,false,fn(item,found)=>predicate(item)||found) {true=>normalize;false=>normalize;};};
   };
  };
 };
}
