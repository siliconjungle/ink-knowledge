module ordered_vector_products;

pub fn words(xs:List<u32>,seed:Vec2<u32>)->Vec2<u32>{
 return vec2(foldl(xs,seed.x,fn(x,s)=>s*3+x),foldl(xs,seed.y,fn(x,s)=>(s+x)^17));
}
pub fn floating(xs:List<f32>,a:f32,b:f32)->Vec3<f32>{
 return vec3(foldl(xs,a,fn(x,s)=>s+x),foldl(xs,b,fn(x,s)=>s*x),foldl(xs,a+b,fn(x,s)=>(s+x)*x));
}
// Each lane preserves the original k order, including wrapping/missing indices.
// The product constructor gives discovery a fixed four-result boundary.
pub fn matrix_tile(a:List<u32>,b:List<u32>,side:u32,row:u32,col:u32)->Vec4<u32>{
 return vec4(
  repeat_until(side,side-side,fn(s)=>false,fn(k,s)=>s+a.at_or(row*side+k,0)*b.at_or(k*side+col,0)),
  repeat_until(side,side-side,fn(s)=>false,fn(k,s)=>s+a.at_or(row*side+k,0)*b.at_or(k*side+col+1,0)),
  repeat_until(side,side-side,fn(s)=>false,fn(k,s)=>s+a.at_or(row*side+k,0)*b.at_or(k*side+col+2,0)),
  repeat_until(side,side-side,fn(s)=>false,fn(k,s)=>s+a.at_or(row*side+k,0)*b.at_or(k*side+col+3,0)));
}
