module ink.knowledge.weighted_cursor;
import "weighted_sequence.ink" as sequence;
// Ordinary measured-sequence cursor. Correctness assumes the usual maintained
// tree invariant. All mutation wrappers either preserve its visible rank using
// adjacency, or invalidate it; callers must use these wrappers for mutation.
record Tree<T>{nodes:Buffer<sequence.Node<T>>,root:u32,first:u32,last:u32,fallback:T,
 hint:u32,start:u32,valid:Bool,safe:Bool,}
record Position<T>{tree:Tree<T>,node:u32,rank:u32,offset:u32,}
fn nil<T>(value:T)->sequence.Node<T>{return sequence.nil<T>(value);}
fn plain<T>(t:Tree<T>)->sequence.Tree<T>{
 return sequence.Tree<T>{nodes:t.nodes,root:t.root,first:t.first,last:t.last,fallback:t.fallback};
}
fn wrapped<T>(t:sequence.Tree<T>,hint:u32,start:u32,valid:Bool,safe:Bool)->Tree<T>{
 return Tree<T>{nodes:t.nodes,root:t.root,first:t.first,last:t.last,fallback:t.fallback,hint:hint,start:start,valid:valid,safe:safe};
}
fn empty<T>(value:T)->Tree<T>{return wrapped<T>(sequence.empty<T>(value),0,0,false,true);}
fn insert_before<T>(t:Tree<T>,before:u32,value:T,extent:u32,weight:u32)->Tree<T>{
 let hint=t.hint;let old=t.nodes.at_or(hint,nil<T>(t.fallback));
 let at=t.start+choose(before==hint,0,old.weight);let fresh=t.nodes.len();
 let root=t.nodes.at_or(t.root,nil<T>(t.fallback));
 let safe=t.safe && weight<=4294967295-root.live;
 let valid=t.valid && safe && hint!=0 && (before==hint || before==old.next);
 return wrapped<T>(sequence.insert_before<T>(plain<T>(t),before,value,extent,weight),fresh,at,valid,safe);
}
fn set_weight<T>(t:Tree<T>,slot:u32,weight:u32)->Tree<T>{
 let hint=t.hint;let start=t.start;let root=t.nodes.at_or(t.root,nil<T>(t.fallback));
 let old=t.nodes.at_or(slot,nil<T>(t.fallback));
 let safe=t.safe && (slot==0 || weight<=4294967295-(root.live-old.weight));
 let valid=t.valid && safe && (slot==0 || slot==hint);
 return wrapped<T>(sequence.set_weight<T>(plain<T>(t),slot,weight),hint,start,valid,safe);
}
fn set_extent<T>(t:Tree<T>,slot:u32,extent:u32,weight:u32)->Tree<T>{
 let hint=t.hint;let start=t.start;let root=t.nodes.at_or(t.root,nil<T>(t.fallback));
 let old=t.nodes.at_or(slot,nil<T>(t.fallback));
 let safe=t.safe && (slot==0 || weight<=4294967295-(root.live-old.weight));
 let valid=t.valid && safe && (slot==0 || slot==hint);
 return wrapped<T>(sequence.set_extent<T>(plain<T>(t),slot,extent,weight),hint,start,valid,safe);
}
fn rank<T>(t:Tree<T>,slot:u32,visible:Bool)->Position<T>{
 let hint=t.hint;let start=t.start;let valid=t.valid;let safe=t.safe;
 let p=sequence.rank<T>(plain<T>(t),slot,visible);
 return Position<T>{tree:wrapped<T>(p.tree,hint,start,valid,safe),node:p.node,rank:p.rank,offset:p.offset};
}
record Nearby<T>{tree:Tree<T>,node:u32,start:u32,found:Bool,done:Bool,}
fn nearby_step<T>(c:Nearby<T>,position:u32)->Nearby<T>{
 if c.node==0{return Nearby<T>{..c,done:true};}
 let n=c.tree.nodes.at_or(c.node,nil<T>(c.tree.fallback));
 if position>=c.start && position-c.start<n.weight{return Nearby<T>{..c,found:true,done:true};}
 if position<c.start{
  let previous=c.tree.nodes.at_or(n.previous,nil<T>(c.tree.fallback));
  return Nearby<T>{..c,node:n.previous,start:c.start-previous.weight};
 }
 return Nearby<T>{..c,node:n.next,start:c.start+n.weight};
}
fn seek<T>(t:Tree<T>,position:u32,visible:Bool)->Position<T>{
 if !visible{return ordinary<T>(t,position,visible);}
 if !t.valid || !t.safe || t.hint==0{return ordinary<T>(t,position,true);}
 let hint=t.hint;let start=t.start;
 let c=repeat_until(8,Nearby<T>{tree:t,node:hint,start:start,found:false,done:false},fn(c)=>c.done,fn(i,c)=>nearby_step<T>(c,position));
 if !c.found{return ordinary<T>(c.tree,position,true);}
 let node=c.node;let start=c.start;
 return Position<T>{tree:Tree<T>{..c.tree,hint:node,start:start,valid:true},node:node,rank:4294967295,offset:position-start};
}
fn ordinary<T>(t:Tree<T>,position:u32,visible:Bool)->Position<T>{
 let hint=t.hint;let start=t.start;let valid=t.valid;let safe=t.safe;
 let p=sequence.seek<T>(plain<T>(t),position,visible);let node=p.node;let rank=p.rank;let offset=p.offset;
 // The baseline traversal uses MAX as its termination sentinel. Preserve its
 // exact boundary result without treating that sentinel query as membership.
 let cache=safe && visible && position!=4294967295 && node!=0 && rank==4294967295;
 let tree=wrapped<T>(p.tree,choose(visible,node,hint),choose(cache,position-offset,start),choose(visible,cache,valid),safe);
 return Position<T>{tree:tree,node:node,rank:rank,offset:offset};
}
