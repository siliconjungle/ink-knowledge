module ink.knowledge.cached_boundary_span_graph;
import "endpoint_index_span_graph.ink" as base;
import "batched_event_graph.ink" as batches;
import "blocked_measure_sequence.ink" as sequence;
import "interval_insert_hint.ink" as insertion;
import "view_pair_causal_workspace.ink" as causal;
import "ragged_builder.ink" as builder;
// Reuse a selection already on a fragment boundary. No tree predicate is
// assumed: zero-offset split is the identity and selection preserves the engine.
// The complete replacement proof is still under construction.
fn delete_step(d:base.Deleting)->base.Deleting{
 let first=base.selected(d.engine,d.position);
 let offset=first.offset;
 let r=choose(offset==0,first,base.selected(base.split(first.engine,first.slot,offset),d.position));
 let s=r.engine.spans.at_or(r.slot,base.nil());let take=choose(d.remaining<s.length,d.remaining,s.length);
 if r.slot==0 || take==0{let e=r.engine;return base.Deleting{..d,engine:base.Engine{..e,error:4},remaining:0};}
 let e=base.split(r.engine,r.slot,take);let s=e.spans.at_or(r.slot,base.nil());let changed=base.Span{..s,deletes:s.deletes+1,deleted:true};
 let target=base.Target{slot:r.slot,id:s.id,length:take,insert:false};
 return base.Deleting{..d,engine:base.Engine{..e,tree:sequence.set_weight<u32>(e.tree,r.slot,0),spans:e.spans.set(r.slot,changed)},targets:builder.push<base.Target>(d.targets,target),remaining:d.remaining-take};
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
 let d=repeat_until(c.remove,base.Deleting{engine:w.engine,targets:builder.begin<base.Target>(w.applied),remaining:c.remove,position:c.position},fn(d)=>d.remaining==0 || d.engine.error!=0,fn(i,d)=>delete_step(d));
 let insertid=c.id+word_widen_u32_to_u64(c.remove);let count=length(c.text);
 let e=choose(count==0,d.engine,base.inserted(d.engine,insertid,c.position,c.text));
 let targets=choose(count==0,d.targets,builder.push<base.Target>(d.targets,base.Target{slot:e.spans.len()-1,id:insertid,length:count,insert:true}));
 return base.Walker{..w,engine:e,graph:causal.append(w.graph,local_parents),applied:builder.finish<base.Target>(targets),last:end-1};
}
