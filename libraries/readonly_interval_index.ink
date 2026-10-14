module ink.knowledge.readonly_interval_index;
import "interval_index.ink" as base;
// Ordinary alternative: immutable index data stays outside the loop state.
// Full source replacement proof is being constructed; tests grant no authority.
record Cursor{node:u32,best:u32,}
fn predecessor(c:Cursor,n:base.Node,key:u64)->Cursor{
 let take=n.start<=key;
 return Cursor{node:choose(take,n.right,n.left),best:choose(take,c.node,c.best)};
}
fn locate(index:base.Index,key:u64)->base.Found{
 let root=index.root;let bound=index.nodes.len();
 let nodes=index.nodes;
 let c=repeat_until(bound,Cursor{node:root,best:0},fn(c)=>c.node==0,fn(i,c)=>predecessor(c,nodes.at_or(c.node,base.nil()),key));
 let n=nodes.at_or(c.best,base.nil());let value=choose(c.best!=0 && (n.end==0 || key<n.end),n.value,0);
 return base.Found{index:base.Index{nodes:nodes,root:root,valid:index.valid},value:value,start:n.start,end:n.end};
}
fn successor_step(c:Cursor,n:base.Node,key:u64)->Cursor{
 let take=n.start>=key;
 return Cursor{node:choose(take,n.left,n.right),best:choose(take,c.node,c.best)};
}
fn successor(index:base.Index,key:u64)->base.Found{
 let root=index.root;let bound=index.nodes.len();let nodes=index.nodes;
 let c=repeat_until(bound,Cursor{node:root,best:0},fn(c)=>c.node==0,fn(i,c)=>successor_step(c,nodes.at_or(c.node,base.nil()),key));
 let n=nodes.at_or(c.best,base.nil());
 return base.Found{index:base.Index{nodes:nodes,root:root,valid:index.valid},value:n.value,start:choose(c.best==0,18446744073709551615,n.start),end:n.end};
}
