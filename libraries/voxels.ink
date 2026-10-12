module ink.knowledge.voxels;
import "buffers.ink" as ranges;
// Dense chunk convention: x varies fastest, then y, then z. Trailing partial
// planes are retained. Invalid dimensions leave the input unchanged.
fn paint_box<T>(cells:List<T>,width:u32,height:u32,x:u32,y:u32,z:u32,nx:u32,ny:u32,nz:u32,value:T)->List<T>{
 let n=length(cells);
 if width==0 || height==0 || width>quot_or(n,height,0) {return cells;}
 let plane=width*height;let depth=quot_or(n,plane,0);
 let x=ranges.minimum(x,width);let y=ranges.minimum(y,height);let z=ranges.minimum(z,depth);
 let nx=ranges.minimum(nx,width-x);let ny=ranges.minimum(ny,height-y);let nz=ranges.minimum(nz,depth-z);
 let b=buffer(cells);
 let b=repeat_until(nz,b,fn(b)=>false,fn(zi)=>fn(b)=>
  repeat_until(ny,b,fn(b)=>false,fn(yi)=>fn(b)=>b.fill_range((z+zi)*plane+(y+yi)*width+x,nx,value)));
 return b.freeze();
}
// Linear addressing is ordinary integer computation and eligible GPU work.
fn linear(x:u32,y:u32,z:u32,width:u32,height:u32)->u32{return (z*height+y)*width+x;}
