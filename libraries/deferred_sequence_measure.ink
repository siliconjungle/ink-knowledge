module ink.knowledge.deferred_sequence_measure;
import "blocked_measure_sequence.ink" as sequence;
// A scoped sequence edit. Prefix queries and structural edits must first flush.
// Stable point edits in one leaf accumulate one modular additive measure delta.
// This source alternative still needs its universal maintained-tree bridge.
record Pending<T>{tree:sequence.Tree<T>,leaf:u32,delta:u32,}
fn begin<T>(tree:sequence.Tree<T>)->Pending<T>{return Pending<T>{tree:tree,leaf:0,delta:0};}
fn flush<T>(p:Pending<T>)->sequence.Tree<T>{
 return choose(p.leaf==0 || p.delta==0,p.tree,sequence.adjusted<T>(p.tree,p.leaf,0,0,0,0,p.delta,0));
}
fn set_weight<T>(p:Pending<T>,slot:u32,weight:u32)->Pending<T>{
 let n=p.tree.nodes.at_or(slot,sequence.nil<T>(p.tree.fallback));
 if slot==0 || slot>=p.tree.nodes.len(){return begin<T>(sequence.set_weight<T>(flush<T>(p),slot,weight));}
 let p=choose(p.leaf==n.leaf,p,Pending<T>{tree:flush<T>(p),leaf:n.leaf,delta:0});
 let tree=p.tree;
 return Pending<T>{tree:sequence.Tree<T>{..tree,nodes:tree.nodes.set(slot,sequence.Node<T>{..n,weight:weight})},leaf:n.leaf,delta:p.delta+weight-n.weight};
}
