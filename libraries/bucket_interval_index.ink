module ink.knowledge.bucket_interval_index;
import "interval_index.ink" as base;
import "interval_fused.ink" as fused;
import "interval_insert_hint.ink" as insertion;
import "interval_partition.ink" as split;
import "interval_cursor.ink" as cursor;
// General disjoint interval forest indexed by the high 32 bits of a u64 key.
// Intervals must stay within a bucket. Node storage and handles are global.
record Index{nodes:Buffer<base.Node>,roots:Map<u64,u32>,valid:Bool,}
record Found{index:Index,value:u32,start:u64,end:u64,hint:u32,}
fn bucket(key:u64)->u64{return wrapping_shr(key,32);}
fn contained(start:u64,end:u64)->Bool{return (start<end || end==0) && bucket(start)==bucket(end-1);}
fn empty()->Index{let i=base.empty();return Index{nodes:i.nodes,roots:Map.empty(),valid:i.valid};}
fn insert(index:Index,start:u64,end:u64,value:u32,hint:u32)->Index{
 if !contained(start,end){return Index{..index,valid:false};}
 let key=bucket(start);let root=index.roots.get_or(key,0);let h=index.nodes.at_or(hint,base.nil());let hint=choose(bucket(h.start)==key,hint,0);
 let i=insertion.insert(base.Index{nodes:index.nodes,root:root,valid:index.valid},start,end,value,hint);
 return Index{nodes:i.nodes,roots:index.roots.set(key,i.root),valid:i.valid};
}
fn locate(index:Index,key:u64,hint:u32)->Found{
 let root=index.roots.get_or(bucket(key),0);let f=cursor.locate(base.Index{nodes:index.nodes,root:root,valid:index.valid},key,hint);
 return Found{index:Index{nodes:f.index.nodes,roots:index.roots,valid:f.index.valid},value:f.value,start:f.start,end:f.end,hint:f.hint};
}
fn partition(index:Index,start:u64,end:u64,cut:u64,value:u32,suffix:u32,hint:u32)->Index{
 if !contained(start,end){return Index{..index,valid:false};}
 let key=bucket(start);let root=index.roots.get_or(key,0);
 let i=split.partition(base.Index{nodes:index.nodes,root:root,valid:index.valid},start,end,cut,value,suffix,hint);
 return Index{nodes:i.nodes,roots:index.roots.set(key,i.root),valid:i.valid};
}
