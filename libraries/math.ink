module ink.knowledge.math;
// Exact, composable algorithms; no compiler math recognisers.
pub fn abs_f32(x:f32)->f32{return f32_from_bits(word_and(f32_bits(x),2147483647));}
pub fn min_f32(a:f32,b:f32)->f32{
 if is_nan(a)||is_nan(b){return f32_from_bits(2143289344);}
 if a==0.0&&b==0.0{return f32_from_bits(word_or(f32_bits(a),f32_bits(b)));}
 return choose(a<b,a,b);
}
pub fn max_f32(a:f32,b:f32)->f32{
 if is_nan(a)||is_nan(b){return f32_from_bits(2143289344);}
 if a==0.0&&b==0.0{return f32_from_bits(word_and(f32_bits(a),f32_bits(b)));}
 return choose(a>b,a,b);
}
pub fn clamp_f32(x:f32,lo:f32,hi:f32)->f32{
 if lo>hi{return f32_from_bits(2143289344);}
 return min_f32(max_f32(x,lo),hi);
}
pub fn min_word<T>(a:T,b:T)->T{return choose(a<b,a,b);}
pub fn max_word<T>(a:T,b:T)->T{return choose(a>b,a,b);}
pub fn clamp_word<T>(x:T,lo:T,hi:T)->T{return min_word<T>(max_word<T>(x,lo),hi);}
pub fn length2(v:Vec2<f32>)->f32{
 let m:f32=max_f32(abs_f32(v.x),abs_f32(v.y));
 if m==0.0{return 0.0;}
 if is_finite(m)==false{return m;}
 let x:f32=v.x/m;let y:f32=v.y/m;
 return m*sqrt(x*x+y*y);
}
pub fn length3(v:Vec3<f32>)->f32{
 let m:f32=max_f32(max_f32(abs_f32(v.x),abs_f32(v.y)),abs_f32(v.z));
 if m==0.0{return 0.0;}
 if is_finite(m)==false{return m;}
 let x:f32=v.x/m;let y:f32=v.y/m;let z:f32=v.z/m;
 return m*sqrt(x*x+y*y+z*z);
}
pub fn normalise2(v:Vec2<f32>)->Option<Vec2<f32>>{
 let m:f32=max_f32(abs_f32(v.x),abs_f32(v.y));
 if m==0.0||is_finite(m)==false{return None;}
 let x:f32=v.x/m;let y:f32=v.y/m;let d:f32=sqrt(x*x+y*y);
 return Some(vec2(x/d,y/d));
}
pub fn normalise3(v:Vec3<f32>)->Option<Vec3<f32>>{
 let m:f32=max_f32(max_f32(abs_f32(v.x),abs_f32(v.y)),abs_f32(v.z));
 if m==0.0||is_finite(m)==false{return None;}
 let x:f32=v.x/m;let y:f32=v.y/m;let z:f32=v.z/m;let d:f32=sqrt(x*x+y*y+z*z);
 return Some(vec3(x/d,y/d,z/d));
}
// Explicit bounded approximations. Outside the stated domain: None.
// Named approximation operations do not authorise replacing exact arithmetic.
pub fn sin_approx(x:f32)->Option<f32>{
 if is_finite(x)==false||abs_f32(x)>3.1415927410125732{return None;}
 let t:f32=x*x;
 return Some(x*(1.0+t*(-0.16666666666666666+t*(0.008333333333333333+t*(-0.0001984126984126984+t*(2.7557319223985893e-06+t*(-2.505210838544172e-08+t*(1.6059043836821613e-10+t*(-7.647163731819816e-13+t*2.8114572543455206e-15)))))))));
}
pub fn cos_approx(x:f32)->Option<f32>{
 if is_finite(x)==false||abs_f32(x)>3.1415927410125732{return None;}
 let t:f32=x*x;
 return Some((1.0+t*(-0.5+t*(0.041666666666666664+t*(-0.001388888888888889+t*(2.48015873015873e-05+t*(-2.755731922398589e-07+t*(2.08767569878681e-09+t*(-1.1470745597729725e-11+t*(4.779477332387385e-14+t*-1.5619206968586225e-16))))))))));
}
pub fn exp_approx(x:f32)->Option<f32>{
 if is_finite(x)==false||abs_f32(x)>80.0{return None;}
 let nf:f32=round_ties_even(x*1.4426950408889634);
 let n:i32=i32_from_f32(nf).fold(fn(v)=>v,fn(u)=>0);
 let r:f32=(x-nf*0.693145751953125)-nf*0.000001428606765330187;
 let p:f32=1.0+r*(1.0+r*(0.5+r*(0.16666666666666666+r*(0.041666666666666664+r*(0.008333333333333333+r*(0.001388888888888889+r*0.0001984126984126984))))));
 let scale:u32=u32_from_f32(f32_from_i32(n+127)).fold(fn(v)=>v,fn(u)=>0);
 return Some(p*f32_from_bits(wrapping_shl(scale,23)));
}
pub fn log_approx(x:f32)->Option<f32>{
 if is_finite(x)==false||x<=0.0{return None;}
 // Scaling subnormals makes exponent extraction independent of underflow.
 let scaled:f32=choose(x<0.000000000000000000000000000000000000011754943508222875,x*8388608.0,x);
 let correction:f32=choose(x<0.000000000000000000000000000000000000011754943508222875,23.0,0.0);
 let b:u32=f32_bits(scaled);let e:f32=f32_from_u32(wrapping_shr(b,23))-127.0-correction;
 let m:f32=f32_from_bits(word_or(word_and(b,8388607),1065353216));
 let z:f32=(m-1.0)/(m+1.0);let t:f32=z*z;
 let p:f32=2.0*z*(1.0+t*(0.3333333333333333+t*(0.2+t*(0.14285714285714285+t*(0.1111111111111111+t*(0.09090909090909091+t*(0.07692307692307693+t*0.06666666666666667)))))));
 return Some(e*0.6931471805599453+p);
}
pub fn exp2_approx(x:f32)->Option<f32>{return exp_approx(x*0.6931471805599453);}
pub fn log2_approx(x:f32)->Option<f32>{return log_approx(x).map(fn(v)=>v*1.4426950408889634);}
