module ink.knowledge.deferred_measure_updates;
import "blocked_measure_sequence.ink" as base;
// Ordinary library alternative: defer additive ancestor updates for one leaf.
// Flush before observing subtree measures or changing structural links.
record Pending<T>{tree:base.Tree<T>,leaf:u32,old:u32,new:u32,}
fn begin<T>(tree:base.Tree<T>)->Pending<T>{return Pending<T>{tree:tree,leaf:0,old:0,new:0};}
fn flush<T>(p:Pending<T>)->Pending<T>{
 if p.leaf==0{return p;}
 return Pending<T>{tree:base.adjusted<T>(p.tree,p.leaf,0,p.old,0,0,p.new,0),leaf:0,old:0,new:0};
}
fn set_weight<T>(p:Pending<T>,slot:u32,weight:u32)->Pending<T>{
 if slot==0{return p;}
 let n=p.tree.nodes.at_or(slot,base.nil<T>(p.tree.fallback));
 if n.weight==weight{return p;}
 let p=choose(p.leaf!=0 && p.leaf!=n.leaf,flush<T>(p),p);
 let tree=p.tree;let nodes=tree.nodes.set(slot,base.Node<T>{..n,weight:weight});
 return Pending<T>{tree:base.Tree<T>{..tree,nodes:nodes},leaf:n.leaf,old:p.old+n.weight,new:p.new+weight};
}
fn finish<T>(p:Pending<T>)->base.Tree<T>{return flush<T>(p).tree;}
