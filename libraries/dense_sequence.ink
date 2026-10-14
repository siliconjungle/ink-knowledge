module ink.knowledge.dense_sequence;
import "gap_sequence.ink" as gap;
// General stable-handle sequence for small working sets. Order is dense;
// payloads/weights have stable slots, and rank caches are updated after insert.
record Node<T>{value:T,previous:u32,next:u32,weight:u32,rank:u32,live:u32,}
record Tree<T>{nodes:Buffer<Node<T>>,order:gap.Gap<u32>,first:u32,last:u32,root:u32,fallback:T,}
record Position<T>{tree:Tree<T>,node:u32,rank:u32,}
record Search<T>{tree:Tree<T>,index:u32,position:u32,node:u32,done:Bool,}
record Refresh<T>{tree:Tree<T>,index:u32,}
record Read<T>{tree:Tree<T>,index:u32,values:Buffer<T>,}
fn nil<T>(value:T)->Node<T>{return Node<T>{value:value,previous:0,next:0,weight:0,rank:0,live:0};}
fn empty<T>(value:T)->Tree<T>{return Tree<T>{nodes:buffer([nil<T>(value)]),order:gap.empty<u32>(0),first:0,last:0,root:0,fallback:value};}
fn item<T>(t:Tree<T>,index:u32)->Position<T>{
 let physical=choose(index<t.order.start,index,index+t.order.end-t.order.start);
 let slot=t.order.data.at_or(physical,0);
 return Position<T>{tree:t,node:slot,rank:index};
}
fn seek_step<T>(s:Search<T>,visible:Bool)->Search<T>{
 let r=item<T>(s.tree,s.index);let n=r.tree.nodes.at_or(r.node,nil<T>(r.tree.fallback));let width=choose(visible,n.weight,1);
 let found=s.position<width;
 return Search<T>{tree:r.tree,index:s.index+1,position:choose(found,s.position,s.position-width),node:choose(found,r.node,0),done:found};
}
fn seek<T>(t:Tree<T>,position:u32,visible:Bool)->Position<T>{
 let bound=t.nodes.len()-1;
 let s=repeat_until(bound,Search<T>{tree:t,index:0,position:position,node:0,done:false},fn(s)=>s.done,fn(i)=>fn(s)=>seek_step<T>(s,visible));
 return Position<T>{tree:s.tree,node:s.node,rank:choose(s.done,4294967295,s.position)};
}
fn rank<T>(t:Tree<T>,slot:u32,visible:Bool)->Position<T>{
 let n=t.nodes.at_or(slot,nil<T>(t.fallback));
 if !visible{return Position<T>{tree:t,node:0,rank:n.rank};}
 let bound=n.rank;
 let s=repeat_until(bound,Search<T>{tree:t,index:0,position:0,node:0,done:false},fn(s)=>false,fn(i)=>fn(s)=>rank_step<T>(s));
 return Position<T>{tree:s.tree,node:0,rank:s.position};
}
fn rank_step<T>(s:Search<T>)->Search<T>{
 let r=item<T>(s.tree,s.index);let n=r.tree.nodes.at_or(r.node,nil<T>(r.tree.fallback));
 return Search<T>{tree:r.tree,index:s.index+1,position:s.position+n.weight,node:0,done:false};
}
fn replaced<T>(n:Node<T>,previous:u32,next:u32,weight:u32,rank:u32,live:u32,value:T)->Node<T>{return Node<T>{value:value,previous:previous,next:next,weight:weight,rank:rank,live:live};}
fn refresh_step<T>(r:Refresh<T>)->Refresh<T>{
 let p=item<T>(r.tree,r.index);let n=p.tree.nodes.at_or(p.node,nil<T>(p.tree.fallback));
 let nodes=p.tree.nodes.set(p.node,replaced<T>(n,n.previous,n.next,n.weight,r.index,n.live,n.value));
 return Refresh<T>{tree:Tree<T>{nodes:nodes,order:p.tree.order,first:p.tree.first,last:p.tree.last,root:0,fallback:p.tree.fallback},index:r.index+1};
}
fn insert_before<T>(t:Tree<T>,before:u32,value:T,weight:u32)->Tree<T>{
 let slot=t.nodes.len();let b=t.nodes.at_or(before,nil<T>(t.fallback));let previous=choose(before==0,t.last,b.previous);
 let position=choose(before==0,slot-1,b.rank);let p=t.nodes.at_or(previous,nil<T>(t.fallback));let root=t.nodes.at_or(0,nil<T>(t.fallback));
 let nodes=t.nodes.push(Node<T>{value:value,previous:previous,next:before,weight:weight,rank:position,live:0});
 let nodes=choose(previous==0,nodes,nodes.set(previous,replaced<T>(p,p.previous,slot,p.weight,p.rank,p.live,p.value)));
 let nodes=choose(before==0,nodes,nodes.set(before,replaced<T>(b,slot,b.next,b.weight,b.rank,b.live,b.value)));
 let nodes=nodes.set(0,replaced<T>(root,0,0,0,0,root.live+weight,root.value));
 let order=gap.inserted<u32>(gap.moved<u32>(t.order,position),slot);
 let t=Tree<T>{nodes:nodes,order:order,first:choose(previous==0,slot,t.first),last:choose(before==0,slot,t.last),root:0,fallback:t.fallback};
 let r=repeat_until(slot-position-1,Refresh<T>{tree:t,index:position+1},fn(r)=>false,fn(i)=>fn(r)=>refresh_step<T>(r));return r.tree;
}
fn set_weight<T>(t:Tree<T>,slot:u32,weight:u32)->Tree<T>{
 if slot==0{return t;}
 let n=t.nodes.at_or(slot,nil<T>(t.fallback));let root=t.nodes.at_or(0,nil<T>(t.fallback));
 let nodes=t.nodes.set(slot,replaced<T>(n,n.previous,n.next,weight,n.rank,n.live,n.value));
 return Tree<T>{nodes:nodes.set(0,replaced<T>(root,0,0,0,0,root.live-n.weight+weight,root.value)),order:t.order,first:t.first,last:t.last,root:0,fallback:t.fallback};
}
fn set_value<T>(t:Tree<T>,slot:u32,value:T)->Tree<T>{
 if slot==0{return t;}let n=t.nodes.at_or(slot,nil<T>(t.fallback));
 return Tree<T>{nodes:t.nodes.set(slot,replaced<T>(n,n.previous,n.next,n.weight,n.rank,n.live,value)),order:t.order,first:t.first,last:t.last,root:0,fallback:t.fallback};
}
fn read_step<T>(r:Read<T>,visible:Bool)->Read<T>{
 let p=item<T>(r.tree,r.index);let n=p.tree.nodes.at_or(p.node,nil<T>(p.tree.fallback));
 let values=choose(!visible || n.weight!=0,r.values.push(n.value),r.values);
 return Read<T>{tree:p.tree,index:r.index+1,values:values};
}
fn values<T>(t:Tree<T>,visible:Bool)->List<T>{
 let bound=t.nodes.len()-1;let r=repeat_until(bound,Read<T>{tree:t,index:0,values:Buffer.empty()},fn(r)=>false,fn(i)=>fn(r)=>read_step<T>(r,visible));return r.values.freeze();
}
