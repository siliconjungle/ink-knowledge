module ink.knowledge.incremental_blocked_interval_cursor;
import "incremental_blocked_interval_index.ink" as intervals;
record Found{index:intervals.Index,value:u32,start:u64,end:u64,hint:u32,}
fn locate(index:intervals.Index,key:u64,hint:u32)->Found{let f=intervals.hinted(index,key,hint);return Found{index:f.index,value:f.value,start:f.start,end:f.end,hint:f.hint};}
