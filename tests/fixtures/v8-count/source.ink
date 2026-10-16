module count_power_proposals;
record Counts {pop:u32,leading:u32,trailing:u32,}
fn slow(k:u32)->u32{return repeat(1000,k,fn(i)=>fn(a)=>a);}
fn reduce(ks:List<u32>)->u32{return foldl(ks,0,fn(k)=>fn(a)=>a+popcount(wrapping_shl(1,k)));}
pub fn score(ks:List<u32>,cohort:u32)->u32{return reduce(ks)+cohort;}
pub fn samples(ks:List<u32>)->List<Counts>{return ks.map(fn(k)=>Counts{pop:popcount(wrapping_shl(1,k)),leading:leading_zeros(wrapping_shl(1,k)),trailing:trailing_zeros(wrapping_shl(1,k))});}
pub fn strict_k(k:u32)->u32{return popcount(wrapping_shl(1,slow(k)));}
pub fn zero32(x:u32)->Bool{return popcount(x)==0&&leading_zeros(x)==32&&trailing_zeros(x)==32;}
pub fn zero64(x:u64)->Bool{return popcount(x)==0&&leading_zeros(x)==64&&trailing_zeros(x)==64;}
pub fn zero_signed(x:i32)->Bool{return popcount(x)==0&&leading_zeros(x)==32&&trailing_zeros(x)==32;}
