module ink.knowledge.search;

// Lossless prepared canonical JSON: 0=null, 1=Boolean, 2=number token,
// 3=string, 4=array, 5=object. Object edges retain keys; array edge order is
// element order. Scalar values retain exact text. No recursive value encoding.
record Edge { key:String, node:u32, }
record Node { kind:u32, value:String, edges:List<Edge>, }
record Document { nodes:List<Node>, root:u32, }
record Frequency { entry:String, calls:u64, }
record Candidate {
 id:String, source:String, target:String, state:Document,
 default_priority:f64, frequencies:List<Frequency>,
}
fn node(document:Document,index:u32)->Node {
 return document.nodes.at_or(index,Node{kind:0,value:"",edges:[]});
}
fn field(document:Document,index:u32,key:String)->Option<u32> {
 if index>=length(document.nodes) {return None;}
 let parent=node(document,index);
 if parent.kind!=5 {return None;}
 let found:Option<u32>=fold_until(parent.edges,None,fn(edge)=>fn(found)=>edge.key==key,
     fn(edge)=>fn(found)=>choose(edge.key==key,Some(edge.node),found));
 return found.fold(fn(child)=>choose(child<length(document.nodes),Some(child),None),fn(unit)=>None);
}
fn element(document:Document,index:u32,offset:u32)->Option<u32> {
 if index>=length(document.nodes) {return None;}
 let parent=node(document,index);
 if parent.kind!=4 || offset>=length(parent.edges) {return None;}
 let child=parent.edges.at_or(offset,Edge{key:"",node:4294967295}).node;
 return choose(child<length(document.nodes),Some(child),None);
}
