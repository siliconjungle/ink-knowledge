module ink.knowledge.workload_kernels;

// Explicit source algorithms for the cross-domain performance corpus. These
// functions are not rewrite rules and confer no optimisation authority.
record Particle { x:u32, y:u32, vx:u32, vy:u32, }
fn ecs_step(rows:List<Particle>)->List<Particle> {
 return rows.map(fn(p)=>Particle{x:p.x+p.vx,y:p.y+p.vy,vx:p.vx,vy:p.vy});
}

record Transform { parent:u32, x:u32, y:u32, }
record Point { x:u32, y:u32, }
// Topologically ordered translation forest. A parent >= its child index denotes
// a root. Wrapping coordinates make exact comparisons portable.
fn propagate(nodes:List<Transform>)->List<Point> {
 var output:Buffer<Point>=Buffer.empty();
 var i:u32=0;for p in nodes {
  let parent=if p.parent<i {output.at_or(p.parent,Point{x:0,y:0})} else {Point{x:0,y:0}};
  output=output.push(Point{x:p.x+parent.x,y:p.y+parent.y});i=i+1;
 }
 return output.freeze();
}

record Token { start:u32, end:u32, kind:u32, }
fn byte_kind(c:u32)->u32 {
 return if c==32 || c==9 || c==10 || c==13 {0}
  else {if (c>=65 && c<=90) || (c>=97 && c<=122) || c==95 {1}
  else {if c>=48 && c<=57 {2} else {3}}};
}
// ASCII micro-language: identifiers, unsigned decimal numbers, and single-byte
// punctuation. This is a lexer workload, not a JavaScript parser substitute.
fn lex(bytes:List<u32>)->List<Token> {
 var output:Buffer<Token>=Buffer.empty();
 var start:u32=0;var active:u32=0;
 var i:u32=0;for c in bytes {
  let kind=byte_kind(c);
  let continuation=(active==1 && (kind==1 || kind==2)) || (active==2 && kind==2);
  if !continuation {
   if active!=0 {output=output.push(Token{start:start,end:i,kind:active});}
   start=i;active=kind;
  }
  if kind==3 {output=output.push(Token{start:i,end:i+1,kind:3});active=0;}
  i=i+1;
 }
 if active!=0 {output=output.push(Token{start:start,end:length(bytes),kind:active});}
 return output.freeze();
}

record Row { key:u32, value:u32, }
// Dense group domain supplied explicitly. Keys outside it are ignored. Values
// use wrapping u32 sums; SQL adapters must request the same modulo semantics.
fn group_sum(rows:List<Row>,groups:u32)->List<u32> {
 var out:Buffer<u32>=buffer_fill(groups,0);
 for row in rows {
  if row.key<groups {let value=out.at_or(row.key,0)+row.value;out=out.set(row.key,value);}
 }
 return out.freeze();
}

record Box { min_x:u32, min_y:u32, max_x:u32, max_y:u32, }
// Orthographic visibility/collision query. Ordered visible indices, including
// touching edges. BVH and vector alternatives must preserve this observation.
fn visible(boxes:List<Box>,view:Box)->List<u32> {
 var output:Buffer<u32>=Buffer.empty();
 var i:u32=0;for b in boxes {
  if b.min_x<=view.max_x && b.max_x>=view.min_x && b.min_y<=view.max_y && b.max_y>=view.min_y {
   output=output.push(i);
  }
  i=i+1;
 }
 return output.freeze();
}

// Row-major square matrix product in the u32 ring. Missing entries are zero.
// BLAS floating-point products need a separate numerical contract.
fn matmul(a:List<u32>,b:List<u32>,side:u32)->List<u32> {
 let out:Buffer<u32>=Buffer.empty();
 return repeat_until(side,out,fn(out)=>false,fn(i)=>fn(out)=>matrix_row(a,b,side,i,out)).freeze();
}
fn matrix_row(a:List<u32>,b:List<u32>,side:u32,i:u32,out:Buffer<u32>)->Buffer<u32> {
 return repeat_until(side,out,fn(out)=>false,fn(j)=>fn(out)=>out.push(matrix_cell(a,b,side,i,j)));
}
fn matrix_cell(a:List<u32>,b:List<u32>,side:u32,i:u32,j:u32)->u32 {
 return repeat_until(side,0,fn(sum)=>false,fn(k)=>fn(sum)=>sum+a.at_or(i*side+k,0)*b.at_or(k*side+j,0));
}

// Complete unit-cost four-neighbour distance field, FIFO frontier, dense visited
// storage. Blocked/unreachable cells use UINT32_MAX. Width zero is invalid.
record Search { out:Buffer<u32>, queue:Buffer<u32>, head:u32, }
fn distances(grid:List<u32>,width:u32,start:u32)->List<u32> {
 let n=length(grid);let out:Buffer<u32>=buffer_fill(n,4294967295);
 if width==0 || rem_or(n,width,1)!=0 || start>=n || grid.at_or(start,1)!=0 {return out.freeze();}
 let queue:Buffer<u32>=Buffer.empty();
 let s=Search{out:out.set(start,0),queue:queue.push(start),head:0};
 let s=repeat_until(n,s,fn(s)=>s.head>=s.queue.len(),fn(i)=>fn(s)=>search_step(grid,width,s));
 return s.out.freeze();
}
fn search_step(grid:List<u32>,width:u32,s:Search)->Search {
 let node=s.queue.at_or(s.head,0);let x=rem_or(node,width,0);
 let next=s.out.at_or(node,0)+1;let n=length(grid);
 var out:Buffer<u32>=s.out;var queue:Buffer<u32>=s.queue;
 for direction in 0..4 {
  let to=if direction==0 {if x>0 {node-1} else {node}}
   else {if direction==1 {if x+1<width {node+1} else {node}}
   else {if direction==2 {if node>=width {node-width} else {node}}
   else {if width<n-node {node+width} else {node}}}};
  if grid.at_or(to,1)==0 && out.at_or(to,0)==4294967295 {
   out=out.set(to,next);queue=queue.push(to);
  }
 }
 return Search{out:out,queue:queue,head:s.head+1};
}

record Body { x:f32, y:f32, vx:f32, vy:f32, }
// Independent particles with semi-implicit Euler and a floor bounce. This
// measures integration, not broadphase, constraints, or a rigid-body engine.
fn integrate(bodies:List<Body>,dt:f32,gravity:f32)->List<Body> {
 return bodies.map(fn(b)=>advance(b,dt,gravity));
}
fn advance(b:Body,dt:f32,gravity:f32)->Body {
 let vy=b.vy+gravity*dt;let y=b.y+vy*dt;
 return Body{x:b.x+b.vx*dt,y:if y<0.0 {0.0} else {y},vx:b.vx,vy:if y<0.0 {0.0-vy} else {vy}};
}
