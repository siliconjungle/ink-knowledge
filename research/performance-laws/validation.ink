module performance_laws;
fn repeat_subtract(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a-k);}
fn repeat_product(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a+k*k);}
fn repeat_identity(x:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a);}
fn repeat_cancel(x:u32,k:u32)->u32{return repeat(4096,x,fn(i)=>fn(a)=>a+k-k);}
fn scaled_sum(xs:List<u32>,k:u32)->u32{return sum(xs.map(fn(x)=>x*k));}
fn zero_sum(xs:List<u32>)->u32{return sum(xs.map(fn(x)=>0));}
fn mapped_count(xs:List<u32>)->u64{return count(xs.map(fn(x)=>x*x+7));}
fn true_filter_sum(xs:List<u32>)->u32{return sum(xs.filter(fn(x)=>true));}
fn false_filter_count(xs:List<u32>)->u64{return count(xs.filter(fn(x)=>false));}
fn filter_idempotent(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x<7).filter(fn(x)=>x<7);}
fn filter_fusion(xs:List<u32>)->List<u32>{return xs.filter(fn(x)=>x<7).filter(fn(x)=>x>2);}
