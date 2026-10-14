module independent_batches;
record Column { column:u32, total:u32, }
pub fn words(xs:List<u32>,states:List<u32>,factor:u32)->List<u32> {
 return states.map(fn(state)=>foldl(xs,state,fn(item,acc)=>acc*factor+item));
}
pub fn floating(xs:List<f32>,states:List<f32>)->List<f32> {
 return states.map(fn(state)=>foldl(xs,state,fn(item,acc)=>(acc+item)*item));
}
pub fn captured_seed(xs:List<u32>,states:List<u32>)->List<u32> {
 return states.map(fn(seed)=>foldl(xs,seed,fn(item,acc)=>acc*seed+item));
}
pub fn columns(ks:List<u32>,states:List<Column>,a:List<u32>,b:List<u32>,side:u32,row:u32)->List<Column> {
 return states.map(fn(state)=>foldl(ks,state,fn(k,acc)=>Column{
  column:acc.column,total:acc.total+a.at_or(row*side+k,0)*b.at_or(k*side+acc.column,0)}));
}
