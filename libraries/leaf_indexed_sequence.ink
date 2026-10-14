module ink.knowledge.leaf_indexed_sequence;
import "blocked_measure_sequence.ink" as base;
// Ordinary candidate. Executable source is separate from rewrite authority;
// its complete loop-embedding proof is required before planner admission.
record Working<T>{nodes:Buffer<base.Node<T>>,fallback:T,}
record Indexed<T>{tree:Working<T>,index:u32,}
fn step<T>(slot:u32,s:Indexed<T>,block:u32)->Indexed<T>{
 let n=s.tree.nodes.at_or(slot,base.nil<T>(s.tree.fallback));
 return Indexed<T>{tree:Working<T>{nodes:s.tree.nodes.set(slot,base.Node<T>{..n,leaf:block,index:s.index}),fallback:s.tree.fallback},index:s.index+1};
}
fn indexed<T>(t:base.Tree<T>,block:u32)->base.Tree<T>{
 let b=t.blocks.at_or(block,base.empty_block());
 if b.leaf{
  let bound=b.count;let start=b.start;let children=t.children;
  let s=repeat_until(bound,Indexed<T>{tree:Working<T>{nodes:t.nodes,fallback:t.fallback},index:0},fn(s)=>false,fn(i,s)=>step<T>(children.at_or(start+s.index,0),s,block));
  return base.Tree<T>{..t,nodes:s.tree.nodes,children:children,fallback:s.tree.fallback};
 }
 return base.indexed<T>(t,block);
}
