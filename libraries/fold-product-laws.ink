module ink.knowledge.fold_product_laws;
// Two pure observations over the same ordered list can share a traversal.
// This law does not equate different tree paths or authorize state mutation.
record Product{first:u64,second:u64,}
law fold_product<A>(xs:List<A>,left:u64,right:u64,
 first:fn(A,u64)->u64,second:fn(A,u64)->u64){
 foldl(xs,Product{first:left,second:right},fn(item,p)=>Product{first:first(item,p.first),second:second(item,p.second)})
 == Product{first:foldl(xs,left,first),second:foldl(xs,right,second)};
 proof by induction xs generalizing(left,right){
  nil=>normalize;
  cons(head,tail)=>ih(left=first(head,left),right=second(head,right));
 };
}
