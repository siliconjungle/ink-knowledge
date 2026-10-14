module ink.knowledge.run_coalescing_span_graph;
import "endpoint_index_span_graph.ink" as base;
import "cached_boundary_span_graph.ink" as boundary;
import "batched_event_graph.ink" as batches;
import "blocked_measure_sequence.ink" as sequence;
import "interval_index.ink" as intervals;
import "interval_insert_hint.ink" as insertion;
import "view_pair_causal_workspace.ink" as causal;
import "ragged_builder.ink" as builder;
// Ordinary source alternative: adjacent tail insertions share one span and
// identity interval. Historical batch targets retain exact IDs and lengths;
// visibility replay splits those ranges when a concurrent frontier needs it.
// Reachable-state preservation and the full source replacement are unproved.
record TailCandidate{engine:base.Engine,slot:u32,previous:base.Span,interval:intervals.Node,length:u32,end:u64,eligible:Bool,}
fn tail_candidate(e:base.Engine,destination:u32,a:base.Anchors,length:u32)->TailCandidate{
 let slot=e.spans.len()-1;let previous=e.spans.at_or(slot,base.nil());
 let node=e.tree.nodes.at_or(slot,sequence.nil<u32>(0));
 let interval=e.ids.nodes.at_or(previous.interval_slot,intervals.nil());
 let adjacent=previous.id+word_widen_u32_to_u64(previous.length);let end=a.id+word_widen_u32_to_u64(length);
 let geometry=slot!=0 && destination==0 && e.tree.last==slot && node.next==0 && previous.active && !previous.deleted && previous.deletes==0;
 let extent=previous.length!=0 && length!=0 && previous.length<=4294967295-length
  && previous.payload<=4294967295-previous.length && previous.payload+previous.length==e.payload.len()
  && node.extent==previous.length && node.weight==previous.length && node.weight2==0 && node.value==slot;
 let identity=a.id==adjacent && adjacent>previous.id && a.left==adjacent-1 && a.right==0 && previous.right==0
  && wrapping_shr(previous.id,32)==wrapping_shr(a.id,32) && (end==0 || end>a.id);
 let indexed=e.ids.valid && previous.interval_slot!=0 && previous.interval_slot<e.ids.nodes.len()
  && interval.start==previous.id && interval.end==a.id && interval.value==slot && interval.right==0;
 return TailCandidate{engine:e,slot:slot,previous:previous,interval:interval,length:length,end:end,eligible:geometry && extent && identity && indexed};
}
fn extended(candidate:TailCandidate,a:base.Anchors,text:List<u32>)->base.Engine{
 let e=candidate.engine;let previous=candidate.previous;let bound=e.ids.nodes.len();
 let successor=repeat_until(bound,insertion.Ascending{index:e.ids,node:previous.interval_slot,done:false},fn(s)=>s.done,fn(i,s)=>insertion.ascend(s));
 let next=successor.index.nodes.at_or(successor.node,intervals.nil());
 let e=base.Engine{..e,ids:successor.index};
 if !successor.done || (successor.node!=0 && (candidate.end==0 || candidate.end>next.start)){return base.committed(e,0,a,text);}
 let span=base.Span{..previous,length:previous.length+candidate.length};
 let data=foldl(text,e.payload,fn(value,data)=>data.push(value));
 let index=e.ids;let ids=intervals.Index{..index,nodes:index.nodes.set(previous.interval_slot,intervals.Node{..candidate.interval,end:candidate.end})};
 return base.Engine{..e,insert_hint:previous.interval_slot,tree:sequence.set_extent<u32>(e.tree,candidate.slot,span.length,span.length,0),spans:e.spans.set(candidate.slot,span),payload:data,ids:ids};
}
fn committed(e:base.Engine,destination:u32,a:base.Anchors,text:List<u32>)->base.Engine{
 let candidate=tail_candidate(e,destination,a,length(text));
 if !candidate.eligible{return base.committed(candidate.engine,destination,a,text);}
 return extended(candidate,a,text);
}

fn inserted(e:base.Engine,id:u64,position:u32,text:List<u32>)->base.Engine{
 let r=base.anchor_selected(e,choose(position==0,0,position-1));let slot=choose(position==0,0,r.slot);
 let leftrank=choose(slot==0,0,r.rank+r.offset+1);let left_hint=slot;
 let s=r.engine.spans.at_or(slot,base.nil());let left=choose(slot==0,0,s.id+word_widen_u32_to_u64(r.offset));
 let e=base.split(r.engine,slot,r.offset+1);
 let next=choose(slot==0,e.tree.first,e.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next);let bound=e.spans.len();
 let f=repeat_until(bound,base.Find{engine:e,slot:next},fn(f)=>f.slot==0 || f.engine.spans.at_or(f.slot,base.nil()).active,fn(i,f)=>base.next_active(f));
 let rightslot=f.slot;let right=f.engine.spans.at_or(rightslot,base.nil()).id;
 // The selected live span has weight equal to extent; splitting preserves
 // its total prefix. Cursor use validates the stable-slot hint before access.
 let r=base.lookup(f.engine,right,true);let parent=r.rank;let right_hint=r.hint;
 let current=choose(slot==0,r.engine.tree.first,r.engine.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next);let bound=r.engine.spans.len();
 let scan=repeat_until(bound,base.Scan{engine:r.engine,left:leftrank,right:rightslot,parent:parent,left_id:left,right_id:right,current:current,destination:current,scanning:false,done:false},fn(s)=>s.done,fn(i,s)=>base.scan_step(s,id));
 return committed(scan.engine,scan.destination,base.Anchors{id:id,left:left,right:right,left_hint:left_hint,right_hint:right_hint},text);
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
