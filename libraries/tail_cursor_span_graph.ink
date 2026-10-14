module ink.knowledge.tail_cursor_span_graph;
import "endpoint_index_span_graph.ink" as base;
import "run_coalescing_span_graph.ink" as runs;
import "cached_boundary_span_graph.ink" as boundary;
import "batched_event_graph.ink" as batches;
import "blocked_measure_sequence.ink" as sequence;
import "interval_insert_hint.ink" as insertion;
import "view_pair_causal_workspace.ink" as causal;
import "ragged_builder.ink" as builder;
// Retained tail cursor alternative. The append shortcut's full maintained-tree
// reachability/source preservation proof is not yet discharged.
fn inserted(e:base.Engine,id:u64,position:u32,text:List<u32>)->base.Engine{
 let root=e.tree.blocks.at_or(e.tree.root,sequence.empty_block());
 let slot=e.spans.len()-1;let span=e.spans.at_or(slot,base.nil());
 if position!=root.live || slot==0 || slot!=e.tree.last || id!=span.id+word_widen_u32_to_u64(span.length){return base.inserted(e,id,position,text);}
 let anchors=base.Anchors{id:id,left:id-1,right:0,left_hint:slot,right_hint:0};
 let candidate=runs.tail_candidate(e,0,anchors,length(text));
 if !candidate.eligible{return base.inserted(candidate.engine,id,position,text);}
 return runs.extended(candidate,anchors,text);
}
fn apply(w:base.Walker,c:batches.Change)->base.Walker{
 if w.error!=0 || w.engine.error!=0{return w;}
 let codes=foldl(c.text,true,fn(value,ok)=>ok && value<1114112 && !(value>=55296 && value<57344));
 if !batches.valid(c) || !codes{return base.Walker{..w,error:4};}
 let slot=w.applied.ranges.len()+1;let end=c.id+batches.width(c);let hint=w.identities.nodes.len();let identities=insertion.insert(w.identities,c.id,end,slot,w.identity_hint);
 let w=base.Walker{..w,identity_hint:hint,identities:identities};if !w.identities.valid{return base.Walker{..w,error:4};}
 let follows=(w.last==0 && length(c.parents)==0) || (w.last!=0 && length(c.parents)==1 && c.parents.at_or(0,0)==w.last);
 let r=base.resolved(w,c.parents);let local_parents=r.parents;let w=base.prepare_resolved(r.walker,local_parents,follows);if w.error!=0 || w.engine.error!=0{return w;}
 let root=w.engine.tree.blocks.at_or(w.engine.tree.root,sequence.empty_block());
 if c.position>root.live || c.remove>root.live-c.position{return base.Walker{..w,error:4};}
 let d=repeat_until(c.remove,base.Deleting{engine:w.engine,targets:builder.begin<base.Target>(w.applied),remaining:c.remove,position:c.position},fn(d)=>d.remaining==0 || d.engine.error!=0,fn(i,d)=>boundary.delete_step(d));
 let insertid=c.id+word_widen_u32_to_u64(c.remove);let count=length(c.text);
 let e=choose(count==0,d.engine,inserted(d.engine,insertid,c.position,c.text));
 let targets=choose(count==0,d.targets,builder.push<base.Target>(d.targets,base.Target{slot:e.spans.len()-1,id:insertid,length:count,insert:true}));
 return base.Walker{..w,engine:e,graph:causal.append(w.graph,local_parents),applied:builder.finish<base.Target>(targets),last:end-1};
}
