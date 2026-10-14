module ink.knowledge.indexed_sequences;
record IndexedBuild{seen:Map<u32,Bool>,out:Buffer<u32>,}
fn build_step_u32(item:u32,r:IndexedBuild)->IndexedBuild{
 let present:Bool=r.seen.contains(item);
 let seen:Map<u32,Bool>=r.seen.set(item,true);
 let out:Buffer<u32>=r.out;
 if present{return IndexedBuild{seen:seen,out:out};}
 return IndexedBuild{seen:seen,out:out.push(item)};
}
fn normalize_u32(xs:List<u32>)->List<u32>{
 let built:IndexedBuild=foldl(xs,IndexedBuild{seen:Map.empty(),out:Buffer.empty()},fn(item)=>fn(r)=>build_step_u32(item,r));
 return built.out.freeze();
}
fn index_u32(xs:List<u32>)->Map<u32,Bool>{
 return foldr(xs,Map.empty(),fn(item)=>fn(seen)=>seen.set(item,true));
}
fn intersection_indexed_u32(xs:List<u32>,ys:List<u32>)->List<u32>{
 let seen:Map<u32,Bool>=index_u32(ys);
 return xs.filter(fn(item)=>seen.contains(item));
}
fn difference_indexed_u32(xs:List<u32>,ys:List<u32>)->List<u32>{
 let seen:Map<u32,Bool>=index_u32(ys);
 return xs.filter(fn(item)=>!seen.contains(item));
}
