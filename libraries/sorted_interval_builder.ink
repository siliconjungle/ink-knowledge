module ink.knowledge.sorted_interval_builder;
import "interval_index.ink" as intervals;
// Linear Cartesian-tree construction for an already ordered interval stream.
// Node handles and priorities match ordinary insertion. Invalid or unordered
// input uses ordinary insertion, retaining that function's error behaviour.
// This is source code, not a checked replacement law for interval insertion.
record Entry{start:u64,end:u64,value:u32,}
record Build{index:intervals.Index,tail:u32,ordered:Bool,}
record Climb{index:intervals.Index,node:u32,left:u32,}
fn ordinary(entries:List<Entry>)->intervals.Index{
 return foldl(entries,intervals.empty(),fn(e,index)=>intervals.insert(index,e.start,e.end,e.value));
}
fn climbed(c:Climb)->Climb{
 let n=c.index.nodes.at_or(c.node,intervals.nil());
 return Climb{index:c.index,node:n.parent,left:c.node};
}
fn appended(b:Build,e:Entry)->Build{
 if !b.ordered{return b;}
 let prior=b.index.nodes.at_or(b.tail,intervals.nil());
 let ordered=(e.start<e.end || e.end==0) && e.value!=0 &&
  (b.tail==0 || (prior.end!=0 && prior.end<=e.start));
 if !ordered{return Build{..b,ordered:false};}
 let slot=b.index.nodes.len();let priority=intervals.priority(slot);
 let bound=slot;let c=repeat_until(bound,Climb{index:b.index,node:b.tail,left:0},fn(c)=>c.node==0 || c.index.nodes.at_or(c.node,intervals.nil()).priority<=priority,fn(i,c)=>climbed(c));
 let n=intervals.Node{start:e.start,end:e.end,value:e.value,left:c.left,right:0,parent:c.node,priority:priority};
 let parent=c.index.nodes.at_or(c.node,intervals.nil());let left=c.index.nodes.at_or(c.left,intervals.nil());
 let nodes=c.index.nodes.push(n);
 let nodes=choose(c.node==0,nodes,nodes.set(c.node,intervals.Node{..parent,right:slot}));
 let nodes=choose(c.left==0,nodes,nodes.set(c.left,intervals.Node{..left,parent:slot}));
 return Build{index:intervals.Index{nodes:nodes,root:choose(c.node==0,slot,c.index.root),valid:true},tail:slot,ordered:true};
}
fn build(entries:List<Entry>)->intervals.Index{
 let b=foldl(entries,Build{index:intervals.empty(),tail:0,ordered:true},fn(e,b)=>appended(b,e));
 if b.ordered{return b.index;}return ordinary(entries);
}
