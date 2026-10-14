module ink.knowledge.incremental_blocked_interval_partition;
import "incremental_blocked_interval_index.ink" as intervals;
fn partition(index:intervals.Index,start:u64,end:u64,cut:u64,value:u32,suffix:u32,hint:u32)->intervals.Index{return intervals.partition(index,start,end,cut,value,suffix,hint);}
