module ink.knowledge.bulk_measure_sequence;
import "blocked_measure_sequence.ink" as sequence;
// Build the general measured sequence bottom-up. Stable item handles are their
// one-based input ordinals. Subsequent edits use the ordinary sequence library.
// This source algorithm has no planner replacement authority without a bridge.
record Item<T>{value:T,extent:u32,weight:u32,weight2:u32,}
record Leaves<T>{tree:sequence.Tree<T>,level:Buffer<u32>,leaf:u32,offset:u32,}
record Level<T>{tree:sequence.Tree<T>,slots:List<u32>,}
record Parents<T>{tree:sequence.Tree<T>,next:Buffer<u32>,parent:u32,offset:u32,}
fn leaf_item<T>(s:Leaves<T>,item:Item<T>)->Leaves<T>{
 let original=s.tree;let fresh=s.offset==0;let leaf=choose(fresh,original.blocks.len(),s.leaf);
 let start=original.children.len();let blocks=choose(fresh,original.blocks.push(sequence.Block{start:start,count:0,parent:0,index:0,leaf:true,size:0,live:0,second:0}),original.blocks);
 let children=choose(fresh,original.children.append(buffer_fill(33,0)),original.children);
 let level=choose(fresh,s.level.push(leaf),s.level);
 let tree:sequence.Tree<T>=sequence.Tree<T>{..original,blocks:blocks,children:children};
 let slot=tree.nodes.len();let previous=tree.last;let prior:sequence.Node<T>=tree.nodes.at_or(previous,sequence.nil<T>(tree.fallback));
 let node=sequence.Node<T>{value:item.value,previous:previous,next:0,leaf:leaf,index:s.offset,extent:item.extent,weight:item.weight,weight2:item.weight2};
 let nodes=tree.nodes.push(node);let nodes=choose(previous==0,nodes,nodes.set(previous,sequence.Node<T>{value:prior.value,previous:prior.previous,next:slot,leaf:prior.leaf,index:prior.index,extent:prior.extent,weight:prior.weight,weight2:prior.weight2}));
 let block:sequence.Block=tree.blocks.at_or(leaf,sequence.empty_block());
 let blocks=tree.blocks.set(leaf,sequence.Block{..block,count:block.count+1,size:block.size+item.extent,live:block.live+item.weight,second:block.second+item.weight2});
 let children=tree.children.set(block.start+s.offset,slot);
 return Leaves<T>{tree:sequence.Tree<T>{..tree,nodes:nodes,blocks:blocks,children:children,first:choose(previous==0,slot,tree.first),last:slot},level:level,leaf:leaf,offset:choose(s.offset==31,0,s.offset+1)};
}
fn parent_item<T>(s:Parents<T>,slot:u32)->Parents<T>{
 let original=s.tree;let fresh=s.offset==0;let parent=choose(fresh,original.blocks.len(),s.parent);
 let start=original.children.len();let blocks=choose(fresh,original.blocks.push(sequence.Block{start:start,count:0,parent:0,index:0,leaf:false,size:0,live:0,second:0}),original.blocks);
 let children=choose(fresh,original.children.append(buffer_fill(33,0)),original.children);
 let next=choose(fresh,s.next.push(parent),s.next);
 let tree:sequence.Tree<T>=sequence.Tree<T>{..original,blocks:blocks,children:children};
 let child:sequence.Block=tree.blocks.at_or(slot,sequence.empty_block());let block:sequence.Block=tree.blocks.at_or(parent,sequence.empty_block());
 let blocks=tree.blocks.set(slot,sequence.Block{..child,parent:parent,index:s.offset});
 let blocks=blocks.set(parent,sequence.Block{..block,count:block.count+1,size:block.size+child.size,live:block.live+child.live,second:block.second+child.second});
 let children=tree.children.set(block.start+s.offset,slot);
 return Parents<T>{tree:sequence.Tree<T>{..tree,blocks:blocks,children:children},next:next,parent:parent,offset:choose(s.offset==31,0,s.offset+1)};
}
fn parent_level<T>(s:Level<T>)->Level<T>{
 let parents:Parents<T>=foldl(s.slots,Parents<T>{tree:s.tree,next:Buffer.empty(),parent:0,offset:0},fn(slot,p)=>parent_item<T>(p,slot));
 return Level<T>{tree:parents.tree,slots:parents.next.freeze()};
}
fn build<T>(items:List<Item<T>>,fallback:T)->sequence.Tree<T>{
 if length(items)==0{return sequence.empty<T>(fallback);}
 let initial:sequence.Tree<T>=sequence.Tree<T>{nodes:buffer([sequence.nil<T>(fallback)]),blocks:buffer([sequence.empty_block()]),children:Buffer.empty(),root:0,first:0,last:0,fallback:fallback};
 let leaves:Leaves<T>=foldl(items,Leaves<T>{tree:initial,level:Buffer.empty(),leaf:0,offset:0},fn(item,s)=>leaf_item<T>(s,item));
 let slots=leaves.level.freeze();let bound=length(slots);
 let result:Level<T>=repeat_until(bound,Level<T>{tree:leaves.tree,slots:slots},fn(s)=>length(s.slots)<=1,fn(i,s)=>parent_level<T>(s));
 return sequence.Tree<T>{..result.tree,root:result.slots.at_or(0,0)};
}
