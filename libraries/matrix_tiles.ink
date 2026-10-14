module matrix_tiles;
// Four independent output columns share each A load. The k order is unchanged.
// This is an explicit algorithm, not an admitted rewrite or BLAS API.
fn tiled(a:List<u32>,b:List<u32>,side:u32)->List<u32>{
 let out:Buffer<u32>=Buffer.empty();
 return repeat_until(side,out,fn(out)=>false,fn(i)=>fn(out)=>tile_row(a,b,side,i,out)).freeze();
}
fn tile_row(a:List<u32>,b:List<u32>,side:u32,i:u32,out:Buffer<u32>)->Buffer<u32>{
 let blocks=wrapping_shr(side,2) + if (side & 3)==0 {0} else {1};
 return repeat_until(blocks,out,fn(out)=>false,fn(block)=>fn(out)=>append_tile(a,b,side,i,block*4,out));
}
fn append_tile(a:List<u32>,b:List<u32>,side:u32,i:u32,j:u32,out:Buffer<u32>)->Buffer<u32>{
 let zero:u32=0;let seed:Vec4<u32>=vec4(zero,zero,zero,zero);
 let v:Vec4<u32>=repeat_until(side,seed,fn(v)=>false,fn(k)=>fn(v)=>tile_step(a,b,side,i,j,k,v));
 let out=out.push(v.x);
 let out=if j+1<side {out.push(v.y)} else {out};
 let out=if j+2<side {out.push(v.z)} else {out};
 return if j+3<side {out.push(v.w)} else {out};
}

fn tile_step(a:List<u32>,b:List<u32>,side:u32,i:u32,j:u32,k:u32,v:Vec4<u32>)->Vec4<u32>{
 let x=a.at_or(i*side+k,0);let base=k*side+j;
 return vec4(v.x+x*b.at_or(base,0),v.y+x*b.at_or(base+1,0),v.z+x*b.at_or(base+2,0),v.w+x*b.at_or(base+3,0));
}
