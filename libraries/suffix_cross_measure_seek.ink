module ink.knowledge.suffix_cross_measure_seek;
import "suffix_measure_sequence.ink" as sequence;

// Select with one additive measure, return the selected item's prefix in
// another measure. Requires a tree maintained by the sequence constructors.
// A missing selection returns node/rank/offset zero. The offset uses selection
// units; rank is the observation before the item, excluding that offset.
record Seeking<T>{tree:sequence.Tree<T>,block:u32,index:u32,position:u32,rank:u32,node:u32,offset:u32,done:Bool,}
fn step<T>(s:Seeking<T>,selection:u32,observation:u32)->Seeking<T>{
 let b=s.tree.blocks.at_or(s.block,sequence.empty_block());
 if s.index>=b.count{return Seeking<T>{..s,done:true};}
 let slot=s.tree.children.at_or(b.start+s.index,0);
 if b.leaf{
  let n=s.tree.nodes.at_or(slot,sequence.nil<T>(s.tree.fallback));
  let weight=sequence.item_measure<T>(n,selection);
  if s.position>=weight{return Seeking<T>{..s,index:s.index+1,position:s.position-weight,rank:s.rank+sequence.item_measure<T>(n,observation)};}
  return Seeking<T>{..s,node:slot,offset:s.position,done:true};
 }
 let child=s.tree.blocks.at_or(slot,sequence.empty_block());
 let weight=sequence.measured(child,selection);
 if s.position>=weight{return Seeking<T>{..s,index:s.index+1,position:s.position-weight,rank:s.rank+sequence.measured(child,observation)};}
 return Seeking<T>{..s,block:slot,index:0};
}
fn seek<T>(t:sequence.Tree<T>,position:u32,selection:u32,observation:u32)->sequence.Position<T>{
 let root=t.root;let count=t.blocks.len();let bound=choose(count>130150524,4294967295,count*33);
 let s=repeat_until(bound,Seeking<T>{tree:t,block:root,index:0,position:position,rank:0,node:0,offset:0,done:false},fn(s)=>s.done,fn(i,s)=>step<T>(s,selection,observation));
 return sequence.Position<T>{tree:s.tree,node:s.node,rank:choose(s.node==0,0,s.rank),offset:choose(s.node==0,0,s.offset)};
}
