module integer_refinements;
fn slow(x:i32)->i32{return repeat(1000,x,fn(i)=>fn(a)=>a);}
pub fn once(x:i32)->i32{return slow(x);}
pub fn strict_zero(x:i32)->i32{return quot_or(slow(x),0,5);}
pub fn strict_self(x:i32)->i32{return quot_or(slow(x),slow(x),5);}
pub fn lazy_default(x:i32)->i32{return quot_or(x,-1,slow(7));}
pub fn signed_quot(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>quot_or(x,8,fallback));}
pub fn signed_rem(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>rem_or(x,8,fallback));}
pub fn negative_quot(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>quot_or(x,-8,fallback));}
pub fn negative_rem(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>rem_or(x,-8,fallback));}
pub fn minus_quot(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>quot_or(x,-1,fallback));}
pub fn minus_rem(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>rem_or(x,-1,fallback));}
pub fn minimum_quot(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>quot_or(x,-2147483648,fallback));}
pub fn minimum_rem(xs:List<i32>,fallback:i32)->List<i32>{return xs.map(fn(x)=>rem_or(x,-2147483648,fallback));}
pub fn sign_fill(xs:List<i32>)->List<i32>{return xs.map(fn(x)=>wrapping_shr(x,31));}
pub fn unsigned_quot(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>quot_or(x,8,73));}
pub fn unsigned_rem(xs:List<u32>)->List<u32>{return xs.map(fn(x)=>rem_or(x,8,73));}
pub fn wide_quot(xs:List<u64>)->List<u64>{return xs.map(fn(x)=>quot_or(x,8,73));}
pub fn wide_rem(xs:List<u64>)->List<u64>{return xs.map(fn(x)=>rem_or(x,8,73));}
fn slow_wide(x:u64)->u64{return repeat(1000,x,fn(i)=>fn(a)=>a);}
pub fn once_wide(x:u64)->u64{return slow_wide(x);}
pub fn strict_wide_self(x:u64)->u64{return quot_or(slow_wide(x),slow_wide(x),slow_wide(73));}
pub fn wide_self(xs:List<u64>,fallback:u64)->List<u64>{return xs.map(fn(x)=>quot_or(x,x,fallback));}
