module ink.knowledge.deferred_delta_laws;
record Delta{old:u32,new:u32,}
law old_offset(xs:List<Delta>,total:u32,initial:u32){
 foldl(xs,total,fn(d,value)=>value+d.old)==total-initial+foldl(xs,initial,fn(d,value)=>value+d.old);
 proof by induction xs generalizing(total,initial){
  nil=>normalize;
  cons(head,tail)=>ih(total=total+head.old,initial=initial+head.old);
 };
}
law new_offset(xs:List<Delta>,total:u32,initial:u32){
 foldl(xs,total,fn(d,value)=>value+d.new)==total-initial+foldl(xs,initial,fn(d,value)=>value+d.new);
 proof by induction xs generalizing(total,initial){
  nil=>normalize;
  cons(head,tail)=>ih(total=total+head.new,initial=initial+head.new);
 };
}
law combine_deltas(xs:List<Delta>,total:u32,old:u32,new:u32){
 foldl(xs,total,fn(d,value)=>value-d.old+d.new)
  == total+old-new-foldl(xs,old,fn(d,value)=>value+d.old)+foldl(xs,new,fn(d,value)=>value+d.new);
 proof by induction xs generalizing(total,old,new){
  nil=>normalize;
  cons(head,tail)=>ih(total=total-head.old+head.new,old=old+head.old,new=new+head.new);
 };
}
law bulk_deltas(xs:List<Delta>,total:u32){
 foldl(xs,total,fn(d,value)=>value-d.old+d.new)
  == total-foldl(xs,0,fn(d,value)=>value+d.old)+foldl(xs,0,fn(d,value)=>value+d.new);
 proof by use combine_deltas(xs,total,0,0);
}
