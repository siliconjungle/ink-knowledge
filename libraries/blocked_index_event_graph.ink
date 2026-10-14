module ink.knowledge.blocked_index_event_graph;
import "batched_event_graph.ink" as batches;
import "blocked_index_span_graph.ink" as ordinary;
import "checkpoint_blocked_index_span_graph.ink" as spans;
import "text_crdts.ink" as reference;
import "gap_sequence.ink" as gap;
import "causal_ranges.ink" as dag;
import "dense_causal_cuts.ink" as cuts;
import "blocked_interval_index.ink" as intervals;
import "blocked_interval_index.ink" as fused_intervals;
// Experimental source alternative. Critical-prefix shredding still needs its
// concrete preservation proof before this can be a database rewrite.
record Chain{last:u64,run:u32,found:Bool,}
fn chain_step(x:Chain,c:batches.Change,minimum:u32)->Chain{
 let follows=choose(x.last==0,length(c.parents)==0,length(c.parents)==1 && c.parents.at_or(0,0)==x.last);
 let run=choose(follows,x.run+1,0);
 return Chain{last:c.id+batches.width(c)-1,run:run,found:x.found || run>=minimum};
}
fn long_chain(changes:List<batches.Change>,minimum:u32)->Bool{
 return foldl(changes,Chain{last:0,run:0,found:false},fn(c,x)=>chain_step(x,c,minimum)).found;
}
record Built{graph:dag.Graph,ends:Map<u64,u32>,identities:intervals.Index,error:u32,}
fn built_step(b:Built,c:batches.Change)->Built{
 if b.error!=0{return b;}
 let codes=foldl(c.text,true,fn(value,ok)=>ok && value<1114112 && !(value>=55296 && value<57344));
 if !batches.valid(c) || !codes{return Built{..b,error:4};}
 let slot=b.graph.nodes.len();let end=c.id+batches.width(c);
 let identities=fused_intervals.insert(b.identities,c.id,end,slot);
 if !identities.valid{return Built{..b,identities:identities,error:4};}
 var ends:Map<u64,u32>=b.ends;var parents:Buffer<u32>=Buffer.empty();
 for p in c.parents{parents=parents.push(ends.get_or(p,0));ends=ends;}
 let graph=dag.append(b.graph,parents.freeze());let valid=graph.valid;
 return Built{graph:graph,ends:ends.set(end-1,slot),identities:identities,error:choose(valid,0,4)};
}
record Enabling{flags:List<Bool>,values:Buffer<Bool>,index:u32,run:u32,minimum:u32,}
fn enable_step(e:Enabling)->Enabling{
 let index=e.index-1;let run=choose(e.flags.at_or(index,false),e.run+1,0);
 return Enabling{..e,values:e.values.set(index,e.flags.at_or(index,false) && run>=e.minimum),index:index,run:run};
}
fn long_flags(flags:List<Bool>,minimum:u32)->List<Bool>{
 let bound=length(flags);let e=repeat_until(bound,Enabling{flags:flags,values:buffer_fill(bound,false),index:bound,run:0,minimum:minimum},fn(e)=>e.index==0,fn(i,e)=>enable_step(e));
 return e.values.freeze();
}
record Plan{flags:List<Bool>,fast:List<Bool>,ends:Map<u64,u32>,valid:Bool,}
fn prepared(changes:List<batches.Change>,minimum:u32)->Plan{
 var b:Built=Built{graph:dag.empty(),ends:Map.empty(),identities:intervals.empty(),error:0};
 for c in changes{b=built_step(b,c);}
 if b.error!=0{return Plan{flags:[],fast:[],ends:b.ends,valid:false};}
 let k=cuts.critical(b.graph);let valid=k.valid;let flags=k.cuts;let fast=long_flags(flags,minimum);
 return Plan{flags:flags,fast:fast,ends:b.ends,valid:valid};
}
record Process{data:gap.Gap<u32>,walker:spans.Walker,gap:Bool,last:u64,index:u32,
 checkpoint:u32,base_end:u64,flags:List<Bool>,fast:List<Bool>,ends:Map<u64,u32>,error:u32,}
fn begin_span(p:Process)->Process{
 let content=gap.freeze<u32>(p.data);let w=spans.seed(content,p.last);
 return Process{..p,data:gap.empty<u32>(0),walker:w,gap:false,checkpoint:p.index-1,base_end:p.last};
}
fn gap_content(p:Process,content:List<u32>)->Process{
 let n=length(content);return Process{..p,data:gap.Gap<u32>{data:buffer(content),start:n,end:n,fallback:0},walker:spans.empty(),gap:true};
}
record Finished{valid:Bool,content:List<u32>,}
fn finished(result:Result<List<u32>,reference.Error>)->Finished{
 return match result{
  Ok(content)=>Finished{valid:true,content:content},
  Err(error)=>Finished{valid:false,content:[]},
 };
}
fn gap_result(p:Process,result:Result<List<u32>,reference.Error>)->Process{
 let out=finished(result);if !out.valid{return Process{..p,error:4};}
 return gap_content(p,out.content);
}
fn begin_gap(p:Process)->Process{
 let result=spans.finish(p.walker);let p=Process{..p,walker:spans.empty()};
 return gap_result(p,result);
}
fn gap_step(p:Process,c:batches.Change)->Process{
 let n=p.data.data.len()-p.data.end+p.data.start;
 if c.position>n || c.remove>n-c.position{return Process{..p,error:4};}
 let data=gap.inserted_many<u32>(gap.erased<u32>(gap.moved<u32>(p.data,c.position),c.remove),c.text);
 return Process{..p,data:data,last:c.id+batches.width(c)-1,index:p.index+1};
}
record Normal{process:Process,parents:List<u64>,}
fn normalized(p:Process,parents:List<u64>)->Normal{
 let checkpoint=p.checkpoint;let base=p.base_end;
 var ends:Map<u64,u32>=p.ends;var values:Buffer<u64>=Buffer.empty();
 for parent in parents{values=values.push(choose(ends.get_or(parent,4294967295)<=checkpoint,base,parent));ends=ends;}
 return Normal{process:Process{..p,ends:ends},parents:values.freeze()};
}
fn span_step(p:Process,c:batches.Change)->Process{
 let n=normalized(p,c.parents);let p=n.process;let w=spans.apply_parents(p.walker,c,n.parents);
 return Process{..p,walker:w,last:c.id+batches.width(c)-1,index:p.index+1};
}
fn process_step(p:Process,c:batches.Change)->Process{
 if p.error!=0{return p;}
 let follows=choose(p.last==0,length(c.parents)==0,length(c.parents)==1 && c.parents.at_or(0,0)==p.last);
 let fast=p.fast.at_or(p.index,false) && p.flags.at_or(p.index-1,false) && follows;
 if p.gap{return choose(fast,gap_step(p,c),span_step(begin_span(p),c));}
 return choose(fast,gap_step(begin_gap(p),c),span_step(p,c));
}
fn phased(changes:List<batches.Change>,plan:Plan)->Result<List<u32>,reference.Error>{
 var p:Process=Process{data:gap.empty<u32>(0),walker:spans.empty(),gap:true,last:0,index:1,checkpoint:0,base_end:0,flags:plan.flags,fast:plan.fast,ends:plan.ends,error:0};
 for c in changes{p=process_step(p,c);}
 if p.error!=0{return Err(reference.Error.InvalidOperation);}
 return choose(p.gap,Ok(gap.freeze<u32>(p.data)),spans.finish(p.walker));
}
fn materialize_with(changes:List<batches.Change>,minimum:u32)->Result<List<u32>,reference.Error>{
 if batches.is_linear(changes){return batches.linear(changes);}
 if !long_chain(changes,minimum){return ordinary.materialize(changes);}
 let plan=prepared(changes,minimum);if !plan.valid{return ordinary.materialize(changes);}
 let any=foldl(plan.fast,false,fn(marked,any)=>any || marked);
 return choose(any,phased(changes,plan),ordinary.materialize(changes));
}
fn materialize(changes:List<batches.Change>)->Result<List<u32>,reference.Error>{return materialize_with(changes,128);}
