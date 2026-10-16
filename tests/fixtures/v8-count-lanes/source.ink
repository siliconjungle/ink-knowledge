module count_lane_checks;
record Stats {pop:u32,leading:u32,trailing:u32,}
fn slow(x:u64)->u64{return repeat(1000,x,fn(i)=>fn(a)=>a);}
pub fn word(x:u64)->Stats{return Stats{pop:popcount(x),leading:leading_zeros(x),trailing:trailing_zeros(x)};}
pub fn samples(xs:List<u64>)->List<Stats>{return xs.map(fn(x)=>Stats{pop:popcount(x),leading:leading_zeros(x),trailing:trailing_zeros(x)});}
pub fn strict(x:u64)->Stats{return Stats{pop:popcount(slow(x)),leading:leading_zeros(slow(x)),trailing:trailing_zeros(slow(x))};}
pub fn narrow32(x:u32)->Stats{return Stats{pop:popcount(x),leading:leading_zeros(x),trailing:trailing_zeros(x)};}
pub fn signed32(x:i32)->Stats{return Stats{pop:popcount(x),leading:leading_zeros(x),trailing:trailing_zeros(x)};}
