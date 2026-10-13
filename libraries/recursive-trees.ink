module ink.knowledge.recursive_trees;

enum Tree<T> { Leaf(T), Branch(List<Tree<T>>), }

// Arbitrary finite branching and payload types. Recursion follows actual
// immutable subvalues; traversal/layout algorithms remain database source.
fn leaves<T>(tree:Tree<T>)->List<T> {
 let initial:List<T>=[];
 return match tree {
  Tree.Leaf(value)=>[value],
  Tree.Branch(children)=>foldl(children,initial,fn(child)=>fn(acc)=>acc.concat(leaves<T>(child))),
 };
}
fn leaf_count<T>(tree:Tree<T>)->u32 {
 return match tree {
  Tree.Leaf(value)=>1,
  Tree.Branch(children)=>foldl(children,0,fn(child)=>fn(acc)=>acc+leaf_count<T>(child)),
 };
}
fn mirror<T>(tree:Tree<T>)->Tree<T> {
 let initial:List<Tree<T>>=[];
 return match tree {
  Tree.Leaf(value)=>Tree<T>.Leaf(value),
  Tree.Branch(children)=>Tree<T>.Branch(foldl(children,initial,fn(child)=>fn(acc)=>[mirror<T>(child)].concat(acc))),
 };
}
