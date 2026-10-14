module ink.knowledge.checked_trees;
import "invariant-values.ink" as checked;

// A finite, arbitrarily branching recursive value. Uniqueness belongs to each
// payload interface; every nested payload is validated at untrusted ingress.
// Tree fields remain private to this module's ordinary source operations.
abstract record Tree<T> { payload:checked.Unique<T>, children:List<Tree<T>>, }

fn node<T>(payload:checked.Unique<T>,children:List<Tree<T>>)->Tree<T> {
 return Tree<T>{payload:payload,children:children};
}
fn payload<T>(tree:Tree<T>)->checked.Unique<T> {return tree.payload;}
fn children<T>(tree:Tree<T>)->List<Tree<T>> {return tree.children;}
fn payload_items<T>(tree:Tree<T>)->List<T> {return checked.elements<T>(tree.payload);}
fn with_payload<T>(tree:Tree<T>,payload:checked.Unique<T>)->Tree<T> {
 return Tree<T>{payload:payload,children:tree.children};
}
fn with_children<T>(tree:Tree<T>,children:List<Tree<T>>)->Tree<T> {
 return Tree<T>{payload:tree.payload,children:children};
}
