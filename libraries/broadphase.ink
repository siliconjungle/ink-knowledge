module ink.knowledge.broadphase;
// Explicit algorithms. No automatic replacement proof is claimed.
record Box { min_x:f32,min_y:f32,max_x:f32,max_y:f32, }
record Pair { a:u32,b:u32, }
fn empty_box()->Box{return Box{min_x:0.0,min_y:0.0,max_x:0.0,max_y:0.0};}
fn valid(b:Box)->Bool{return is_finite(b.min_x)&&is_finite(b.min_y)&&is_finite(b.max_x)&&is_finite(b.max_y)&&b.min_x<=b.max_x&&b.min_y<=b.max_y;}
fn overlap(a:Box,b:Box)->Bool{return a.min_x<=b.max_x&&a.max_x>=b.min_x&&a.min_y<=b.max_y&&a.max_y>=b.min_y;}
fn ordered_key(x:f32)->u32{let bits=f32_bits(x);return if (bits&2147483648)==0 {bits^2147483648} else {word_not(bits)};}
// Stable radix sorting is ordinary library code over existing bounded buffers.
// Each key access is total. These helpers also serve canonical pair ordering.
fn indices(n:u32)->List<u32>{let out:Buffer<u32>=Buffer.empty();return repeat_until(n,out,fn(out)=>false,fn(i)=>fn(out)=>out.push(i)).freeze();}
fn radix_pass(keys:List<u32>,order:List<u32>,shift:u32)->List<u32>{
 var counts:Buffer<u32>=buffer_fill(256,0);
 for id in order {let bucket=wrapping_shr(keys.at_or(id,0),shift)&255;let previous=counts.at_or(bucket,0);counts=counts.set(bucket,previous+1);}
 let sums=counts.freeze().scan();
 var offsets:Buffer<u32>=buffer_fill(256,0);
 for i in 0..256 {offsets=offsets.set(i,if i==0 {0} else {sums.at_or(i-1,0)});}
 var out:Buffer<u32>=buffer_fill(length(order),0);
 for id in order {let bucket=wrapping_shr(keys.at_or(id,0),shift)&255;let slot=offsets.at_or(bucket,0);out=out.set(slot,id);offsets=offsets.set(bucket,slot+1);}
 return out.freeze();
}
fn radix(keys:List<u32>,order:List<u32>)->List<u32>{
 let shifts:List<u32>=[0,8,16,24];var order:List<u32>=order;for shift in shifts {order=radix_pass(keys,order,shift);}return order;
}
fn canonical(pairs:List<Pair>)->List<Pair>{
 let second=pairs.map(fn(p)=>p.b);let first=pairs.map(fn(p)=>p.a);
 let order=radix(second,indices(length(pairs)));let order=radix(first,order);
 return order.map(fn(i)=>pairs.at_or(i,Pair{a:0,b:0}));
}
fn pair_step(boxes:List<Box>,i:u32,j:u32,out:Buffer<Pair>)->Buffer<Pair>{
 let a=boxes.at_or(i,empty_box());let b=boxes.at_or(j,empty_box());
 return if j>i&&valid(a)&&valid(b)&&overlap(a,b){out.push(Pair{a:i,b:j})}else{out};
}
fn pair_row(boxes:List<Box>,i:u32,out:Buffer<Pair>)->Buffer<Pair>{
 return repeat_until(length(boxes),out,fn(out)=>false,fn(j)=>fn(out)=>pair_step(boxes,i,j,out));
}
fn all_pairs(boxes:List<Box>)->List<Pair>{
 let out:Buffer<Pair>=Buffer.empty();
 return repeat_until(length(boxes),out,fn(out)=>false,fn(i)=>fn(out)=>pair_row(boxes,i,out)).freeze();
}
record Scan { pos:u32,out:Buffer<Pair>, }
fn scan_done(boxes:List<Box>,order:List<u32>,a:Box,s:Scan)->Bool{
 return s.pos>=length(order)||boxes.at_or(order.at_or(s.pos,0),empty_box()).min_x>a.max_x;
}
fn scan_one(boxes:List<Box>,order:List<u32>,id:u32,a:Box,s:Scan)->Scan{
 let other=order.at_or(s.pos,0);let b=boxes.at_or(other,empty_box());
 let out=if overlap(a,b){s.out.push(if id<other {Pair{a:id,b:other}} else {Pair{a:other,b:id}})}else{s.out};
 return Scan{pos:s.pos+1,out:out};
}
fn sweep_row(boxes:List<Box>,order:List<u32>,k:u32,out:Buffer<Pair>)->Buffer<Pair>{
 let id=order.at_or(k,0);let a=boxes.at_or(id,empty_box());let s=Scan{pos:k+1,out:out};
 return repeat_until(length(order),s,fn(s)=>s.pos>=length(order)||boxes.at_or(order.at_or(s.pos,0),empty_box()).min_x>a.max_x,fn(j)=>fn(s)=>scan_one(boxes,order,id,a,s)).out;
}
fn sweep(boxes:List<Box>)->List<Pair>{
 let keys=boxes.map(fn(b)=>ordered_key(b.min_x));
 let order=indices(length(boxes)).filter(fn(i)=>valid(boxes.at_or(i,empty_box())));
 let order=radix(keys,order);let out:Buffer<Pair>=Buffer.empty();
 let out=repeat_until(length(order),out,fn(out)=>false,fn(k)=>fn(out)=>sweep_row(boxes,order,k,out));
 return canonical(out.freeze());
}
// A static binary bounding-volume hierarchy. Sorted leaves are joined in
// adjacent pairs; the query rejects whole subtrees using their union bounds.
// Box2D's dynamic SAH insertion/rotations are a distinct maintained algorithm.
record Node { bounds:Box,left:u32,right:u32,id:u32,leaf:Bool, }
fn empty_node()->Node{return Node{bounds:empty_box(),left:0,right:0,id:0,leaf:true};}
fn union_box(a:Box,b:Box)->Box{return Box{min_x:if a.min_x<b.min_x{a.min_x}else{b.min_x},min_y:if a.min_y<b.min_y{a.min_y}else{b.min_y},max_x:if a.max_x>b.max_x{a.max_x}else{b.max_x},max_y:if a.max_y>b.max_y{a.max_y}else{b.max_y}};}
record Build {nodes:Buffer<Node>,front:List<u32>,}
record Level {nodes:Buffer<Node>,front:Buffer<u32>,}
fn join_nodes(front:List<u32>,i:u32,s:Level)->Level{
 let left=front.at_or(i*2,0);
 if i*2+1>=length(front){return Level{nodes:s.nodes,front:s.front.push(left)};}
 let right=front.at_or(i*2+1,0);let a=s.nodes.at_or(left,empty_node());let b=s.nodes.at_or(right,empty_node());let index=s.nodes.len();
 let nodes=s.nodes.push(Node{bounds:union_box(a.bounds,b.bounds),left:left,right:right,id:0,leaf:false});
 return Level{nodes:nodes,front:s.front.push(index)};
}
fn next_level(s:Build)->Build{
 let width=length(s.front);let count=wrapping_shr(width,1)+(width&1);
 let next:Buffer<u32>=Buffer.empty();let level=Level{nodes:s.nodes,front:next};
 let level=repeat_until(count,level,fn(level)=>false,fn(i)=>fn(level)=>join_nodes(s.front,i,level));
 return Build{nodes:level.nodes,front:level.front.freeze()};
}
record Tree {nodes:List<Node>,root:u32,}
fn build_tree(boxes:List<Box>)->Tree{
 let keys=boxes.map(fn(b)=>ordered_key(b.min_x));let order=indices(length(boxes)).filter(fn(i)=>valid(boxes.at_or(i,empty_box())));let order=radix(keys,order);
 let nodes:Buffer<Node>=buffer(order.map(fn(id)=>Node{bounds:boxes.at_or(id,empty_box()),left:0,right:0,id:id,leaf:true}));
 let s=Build{nodes:nodes,front:indices(length(order))};
 let s=repeat_until(length(order),s,fn(s)=>length(s.front)<=1,fn(i)=>fn(s)=>next_level(s));
 return Tree{nodes:s.nodes.freeze(),root:s.front.at_or(0,0)};
}
record Visit {stack:Buffer<u32>,out:Buffer<Pair>,}
fn visit_step(nodes:List<Node>,id:u32,box:Box,s:Visit)->Visit{
 let index=s.stack.at_or(s.stack.len()-1,0);let stack=s.stack.pop();let node=nodes.at_or(index,empty_node());
 if !overlap(box,node.bounds){return Visit{stack:stack,out:s.out};}
 if node.leaf {return Visit{stack:stack,out:if node.id>id{s.out.push(Pair{a:id,b:node.id})}else{s.out}};}
 return Visit{stack:stack.push(node.left).push(node.right),out:s.out};
}
fn query_tree(boxes:List<Box>,tree:Tree,id:u32,out:Buffer<Pair>)->Buffer<Pair>{
 let box=boxes.at_or(id,empty_box());if !valid(box)||length(tree.nodes)==0{return out;}
 let stack:Buffer<u32>=Buffer.empty();let s=Visit{stack:stack.push(tree.root),out:out};
 return repeat_until(length(tree.nodes),s,fn(s)=>s.stack.len()==0,fn(i)=>fn(s)=>visit_step(tree.nodes,id,box,s)).out;
}
fn bvh(boxes:List<Box>)->List<Pair>{
 let tree=build_tree(boxes);let out:Buffer<Pair>=Buffer.empty();
 let out=repeat_until(length(boxes),out,fn(out)=>false,fn(id)=>fn(out)=>query_tree(boxes,tree,id,out));
 return canonical(out.freeze());
}
