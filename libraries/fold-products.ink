module ink.knowledge.fold_products;
// Fuse independent ordered reductions without associativity or commutativity.
// A carrier may be a record, vector or another representation, but its step
// must prove the whole product equation at every input and pair of states.
law foldl_product<A,L,R,P>(xs:List<A>,left:L,right:R,
 pack:fn(L,R)->P,left_step:fn(A,L)->L,right_step:fn(A,R)->R,step:fn(A,P)->P) {
 assume advances(item:A,l:L,r:R):
  step(item,pack(l,r))==pack(left_step(item,l),right_step(item,r));
 foldl(xs,pack(left,right),fn(item,acc)=>step(item,acc))
  ==pack(foldl(xs,left,fn(item,acc)=>left_step(item,acc)),
         foldl(xs,right,fn(item,acc)=>right_step(item,acc)));
 proof by induction xs generalizing(left,right) {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==foldl(tail,step(head,pack(left,right)),fn(item,acc)=>step(item,acc)) by normalize;
   ==foldl(tail,pack(left_step(head,left),right_step(head,right)),fn(item,acc)=>step(item,acc)) by congruence(normalize,assumption advances(head,left,right),normalize);
   ==_ by ih(left=left_step(head,left),right=right_step(head,right));
  };
 };
}
record Totals { sum:u32, xor:u32, }
law fuse_totals(xs:List<u32>,sum:u32,xor:u32) {
 Totals{sum:foldl(xs,sum,fn(x,s)=>s+x),xor:foldl(xs,xor,fn(x,s)=>s^x)}
  ==foldl(xs,Totals{sum:sum,xor:xor},fn(x,s)=>Totals{sum:s.sum+x,xor:s.xor^x});
 proof by symmetry(use foldl_product<u32,u32,u32,Totals>(xs,sum,xor,
  fn(a,b)=>Totals{sum:a,xor:b},fn(x,s)=>s+x,fn(x,s)=>s^x,
  fn(x,s)=>Totals{sum:s.sum+x,xor:s.xor^x}));
}
record FloatTotals { first:f32, second:f32, }
law fuse_float_totals(xs:List<f32>,a:f32,b:f32) {
 FloatTotals{first:foldl(xs,a,fn(x,s)=>s+x),second:foldl(xs,b,fn(x,s)=>s*x)}
 ==foldl(xs,FloatTotals{first:a,second:b},fn(x,s)=>FloatTotals{first:s.first+x,second:s.second*x});
 proof by symmetry(use foldl_product<f32,f32,f32,FloatTotals>(xs,a,b,
  fn(a,b)=>FloatTotals{first:a,second:b},fn(x,s)=>s+x,fn(x,s)=>s*x,
  fn(x,s)=>FloatTotals{first:s.first+x,second:s.second*x}));
}
// Exact concatenation traversal: blocks may be empty or uneven. Reassociation
// happens only to lists, never to the accumulator's arithmetic.
law foldl_append<A,S>(xs:List<A>,ys:List<A>,s:S,step:fn(A,S)->S) {
 foldl(xs.concat(ys),s,step)==foldl(ys,foldl(xs,s,step),step);
 proof by induction xs generalizing(s) {
  nil=>normalize;
  cons(head,tail)=>ih(s=step(head,s));
 };
}
law foldl_blocks<A,S>(blocks:List<List<A>>,rest:List<A>,s:S,step:fn(A,S)->S) {
 foldl(foldr(blocks,rest,fn(xs,tail)=>xs.concat(tail)),s,step)
 ==foldl(rest,foldl(blocks,s,fn(xs,acc)=>foldl(xs,acc,step)),step);
 proof by induction blocks generalizing(s) {
  nil=>normalize;
  cons(head,tail)=>calc {
   _==foldl(head.concat(foldr(tail,rest,fn(xs,tail)=>xs.concat(tail))),s,step) by normalize;
   ==foldl(foldr(tail,rest,fn(xs,tail)=>xs.concat(tail)),foldl(head,s,step),step)
     by use foldl_append<A,S>(head,foldr(tail,rest,fn(xs,tail)=>xs.concat(tail)),s,step);
   ==_ by ih(s=foldl(head,s,step));
  };
 };
}
