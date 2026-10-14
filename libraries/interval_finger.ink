module ink.knowledge.interval_finger;
import "interval_index.ink" as intervals;
import "interval_cursor.ink" as cursor;
// Local predecessor/successor navigation through maintained parent links.
// Every returned hint validates current bounds; misses retain root lookup.
// Equivalence requires a constructor-maintained disjoint interval tree.
record Down{index:intervals.Index,node:u32,best:u32,}
fn down_step(d:Down,backward:Bool)->Down{
 let n=d.index.nodes.at_or(d.node,intervals.nil());
 return Down{index:d.index,node:choose(backward,n.right,n.left),best:d.node};
}
record Up{index:intervals.Index,node:u32,found:u32,done:Bool,}
fn up_step(u:Up,backward:Bool)->Up{
 let n=u.index.nodes.at_or(u.node,intervals.nil());let p=u.index.nodes.at_or(n.parent,intervals.nil());
 if n.parent==0{return Up{..u,found:0,done:true};}
 let found=choose(backward,p.right==u.node,p.left==u.node);
 return Up{index:u.index,node:n.parent,found:choose(found,n.parent,0),done:found};
}
record Neighbor{index:intervals.Index,node:u32,}
fn neighbor(index:intervals.Index,hint:u32,backward:Bool)->Neighbor{
 let n=index.nodes.at_or(hint,intervals.nil());let child=choose(backward,n.left,n.right);let bound=index.nodes.len();
 if child!=0{
  let d=repeat_until(bound,Down{index:index,node:child,best:0},fn(d)=>d.node==0,fn(i,d)=>down_step(d,backward));
  return Neighbor{index:d.index,node:d.best};
 }
 let u=repeat_until(bound,Up{index:index,node:hint,found:0,done:false},fn(u)=>u.done,fn(i,u)=>up_step(u,backward));
 return Neighbor{index:u.index,node:u.found};
}
fn locate(index:intervals.Index,key:u64,hint:u32)->cursor.Found{
 let n=index.nodes.at_or(hint,intervals.nil());
 if index.valid && hint!=0 && hint<index.nodes.len() && n.value!=0{
  if n.start<=key && (n.end==0 || key<n.end){return cursor.Found{index:index,value:n.value,start:n.start,end:n.end,hint:hint};}
  let f=neighbor(index,hint,key<n.start);let n=f.index.nodes.at_or(f.node,intervals.nil());
  if f.node!=0 && n.value!=0 && n.start<=key && (n.end==0 || key<n.end){return cursor.Found{index:f.index,value:n.value,start:n.start,end:n.end,hint:f.node};}
  return cursor.locate(f.index,key,0);
 }
 return cursor.locate(index,key,0);
}
