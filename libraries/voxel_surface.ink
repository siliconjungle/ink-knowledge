module ink.knowledge.voxel_surface;
record Face { x:u32, y:u32, z:u32, direction:u32, }
// Padded cubic chunks: zero is empty; all other materials are opaque.
// Directions -X,+X,-Y,+Y,-Z,+Z; boundary voxels are neighbors only.
fn face(i:u32,side:u32,direction:u32)->Face {
 return Face{x:rem_or(i,side,0),y:rem_or(quot_or(i,side,0),side,0),z:quot_or(i,side*side,0),direction:direction};
}
fn visible_faces_linear(cells:List<u32>,side:u32)->List<Face>{
 if side<3 || side>quot_or(length(cells),side,0) {return [];}
 let plane=side*side;
 if side>quot_or(length(cells),plane,0) {return [];}
 let output:Buffer<Face>=buffer([]);
 return repeat_until(side*plane,output,fn(output)=>false,fn(i)=>fn(output)=>
 choose(cells.at_or(i,0)!=0 && rem_or(i,side,0)>0 && rem_or(i,side,0)<side-1 && rem_or(quot_or(i,side,0),side,0)>0 && rem_or(quot_or(i,side,0),side,0)<side-1 && quot_or(i,plane,0)>0 && quot_or(i,plane,0)<side-1,repeat_until(6,output,fn(out)=>false,fn(d)=>fn(out)=>choose(cells.at_or(choose(d==0,i-1,choose(d==1,i+1,choose(d==2,i-side,choose(d==3,i+side,choose(d==4,i-plane,i+plane))))),0)==0,out.push(face(i,side,d)),out)),output)).freeze();
}

fn neighbor(i:u32,side:u32,d:u32)->u32 {
 return choose(d==0,i-1,choose(d==1,i+1,choose(d==2,i-side,choose(d==3,i+side,choose(d==4,i-side*side,i+side*side)))));
}
// The same ordered observation with dimension strides carried by loop indices.
// This is an ordinary library algorithm, not a lowering recogniser.
fn visible_faces(cells:List<u32>,side:u32)->List<Face>{
 if side<3 || side>quot_or(length(cells),side,0) {return [];}
 let plane=side*side;
 if side>quot_or(length(cells),plane,0) {return [];}
 let output:Buffer<Face>=buffer([]);
 return repeat_until(side-2,output,fn(out)=>false,fn(z)=>fn(out)=>
 repeat_until(side-2,out,fn(out)=>false,fn(y)=>fn(out)=>
 repeat_until(side-2,out,fn(out)=>false,fn(x)=>fn(out)=>
 choose(cells.at_or(((z+1)*side+(y+1))*side+x+1,0)!=0,
 repeat_until(6,out,fn(out)=>false,fn(d)=>fn(out)=>
 choose(cells.at_or(neighbor(((z+1)*side+(y+1))*side+x+1,side,d),0)==0,out.push(Face{x:x+1,y:y+1,z:z+1,direction:d}),out)),out)))).freeze();
}
