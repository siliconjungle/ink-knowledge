module loop_invariant_checks;
pub fn mapped(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.map(fn(x)=>foldl(ys,0,fn(y)=>fn(a)=>a+y)+x);}
pub fn filtered(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.filter(fn(x)=>x>foldl(ys,0,fn(y)=>fn(a)=>a+y));}
pub fn folded(xs:List<u32>,ys:List<u32>,seed:u32)->u32{return foldl(xs,seed,fn(x)=>fn(a)=>a+x*foldl(ys,0,fn(y)=>fn(b)=>b+y));}
pub fn right(xs:List<u32>,ys:List<u32>,seed:u32)->u32{return foldr(xs,seed,fn(x)=>fn(a)=>a-x*foldl(ys,0,fn(y)=>fn(b)=>b+y));}
pub fn nested(xs:List<u32>,ys:List<u32>,seed:u32)->List<u32>{return xs.map(fn(x)=>foldl(ys,0,fn(y)=>fn(a)=>a+foldl(ys,seed,fn(z)=>fn(b)=>b+z)+y)+x);}
pub fn floats(xs:List<f32>,ys:List<f32>,seed:f32)->List<f32>{return xs.map(fn(x)=>foldl(ys,seed,fn(y)=>fn(a)=>a+y)+x);}
pub fn wide(xs:List<u64>,ys:List<u64>)->List<u64>{return xs.map(fn(x)=>foldl(ys,0,fn(y)=>fn(a)=>a+y)+x);}
pub fn signed(xs:List<i32>,ys:List<i32>)->List<i32>{return xs.map(fn(x)=>foldl(ys,0,fn(y)=>fn(a)=>a+y)+x);}
pub fn booleans(xs:List<u32>,ys:List<u32>)->List<Bool>{return xs.map(fn(x)=>(count(ys.filter(fn(y)=>y>1))>0)==(x>0));}
pub fn captured(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.map(fn(x)=>foldl(ys,0,fn(y)=>fn(a)=>a+foldl(xs,x,fn(z)=>fn(b)=>b+z)+y));}
pub fn whole_choice(xs:List<u32>,ys:List<u32>,c:Bool)->List<u32>{return xs.map(fn(x)=>choose(c,foldl(ys,0,fn(y)=>fn(a)=>a+y),0)+x);}
pub fn dependent(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>foldl(xs,x,fn(y)=>fn(a)=>a+x*y));}
pub fn conditional(xs:List<u32>,ys:List<u32>)->List<u32>{return xs.map(fn(x)=>choose(x>0,foldl(ys,0,fn(y)=>fn(a)=>a+y),0));}
pub fn stopping(xs:List<u32>,ys:List<u32>)->u32{return fold_until(xs,0,fn(x)=>fn(a)=>a>5,fn(x)=>fn(a)=>a+x+foldl(ys,0,fn(y)=>fn(b)=>b+y));}
