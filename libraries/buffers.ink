module ink.knowledge.buffers;
// Algorithms over general owned range primitives. No compiler recognisers.
fn minimum(a:u32,b:u32)->u32 {return choose(a<b,a,b);}
fn erase_range<T>(xs:List<T>,start:u32,count:u32)->List<T>{
 let n=length(xs);let start=minimum(start,n);let count=minimum(count,n-start);
 return buffer(xs).copy_within(start+count,start,n-start-count).truncate(n-count).freeze();
}
fn insert_gap<T>(xs:List<T>,start:u32,count:u32,value:T,maximum:u32)->List<T>{
 let n=length(xs);let start=minimum(start,n);
 // Refuse growth beyond an explicit capacity; subtraction cannot wrap.
 if n>maximum || count>maximum-n {return xs;}
 let b=buffer(xs);
 let b=repeat_until(count,b,fn(b)=>false,fn(i)=>fn(b)=>b.push(value));
 return b.copy_within(start,start+count,n-start).fill_range(start,count,value).freeze();
}
