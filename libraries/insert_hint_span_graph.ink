module ink.knowledge.insert_hint_span_graph;
import "batched_event_graph.ink" as batches;
import "text_crdts.ink" as reference;
import "blocked_measure_sequence.ink" as sequence;
import "cross_measure_seek.ink" as cross;
import "interval_index.ink" as intervals;
import "interval_fused.ink" as fused_intervals;
import "interval_insert_hint.ink" as insertion;
import "interval_partition.ink" as partition;
import "interval_cursor.ink" as cursor;
import "refinement_span.ink" as refinement;
import "view_pair_causal_workspace.ink" as causal;
import "ragged_buffer.ink" as ragged;
import "ragged_builder.ink" as builder;

// Ordinary source implementation. Causal nodes represent complete batches;
// insertion identities, payloads and temporary visibility are stored in runs.
// Interior batch frontiers use the scalar implementation until DAG splitting
// is implemented. This is not an admitted optimisation of that implementation.
record Span{interval_slot:u32,next_fragment:u32,id:u64,left:u64,right:u64,left_hint:u32,right_hint:u32,length:u32,payload:u32,active:Bool,deletes:u32,deleted:Bool,}
record Engine{insert_hint:u32,tree:sequence.Tree<u32>,spans:Buffer<Span>,payload:Buffer<u32>,ids:intervals.Index,error:u32,}
record Located{engine:Engine,slot:u32,offset:u32,rank:u32,hint:u32,}
record Scan{engine:Engine,left:u32,right:u32,parent:u32,left_id:u64,right_id:u64,current:u32,destination:u32,scanning:Bool,done:Bool,}
record Target{slot:u32,id:u64,length:u32,insert:Bool,}
record Walker{engine:Engine,graph:causal.Graph,ends:Map<u64,u32>,identities:intervals.Index,
 applied:ragged.Rows<Target>,last:u64,error:u32,}
record Find{engine:Engine,slot:u32,}
record Deleting{engine:Engine,targets:builder.Pending<Target>,remaining:u32,position:u32,}
record Toggling{engine:Engine,slot:u32,id:u64,remaining:u32,}
record Walking{walker:Walker,index:u32,}
record Output{engine:Engine,slot:u32,values:Buffer<u32>,}
record Eligibility{ends:Map<u64,Bool>,valid:Bool,}

fn nil()->Span{return Span{interval_slot:0,next_fragment:0,id:0,left:0,right:0,left_hint:0,right_hint:0,length:0,payload:0,active:false,deletes:0,deleted:true};}
fn empty_engine()->Engine{return Engine{insert_hint:0,tree:sequence.empty<u32>(0),spans:buffer([nil()]),payload:Buffer.empty(),ids:intervals.empty(),error:0};}
fn empty()->Walker{return Walker{engine:empty_engine(),graph:causal.empty(),ends:Map.empty(),identities:intervals.empty(),applied:ragged.empty<Target>(),last:0,error:0};}
fn weight(s:Span)->u32{return choose(s.active && s.deletes==0,s.length,0);}
fn lookup(e:Engine,id:u64,right:Bool)->Located{return hinted_lookup(e,id,right,0);}
fn hinted_lookup(e:Engine,id:u64,right:Bool,hint:u32)->Located{
 if id==0{let root=e.tree.blocks.at_or(e.tree.root,sequence.empty_block());return Located{engine:e,slot:0,offset:0,rank:choose(right,root.size+1,0),hint:0};}
 let f=cursor.locate(e.ids,id,hint);let slot=f.value;let span=e.spans.at_or(slot,nil());
 let offset=word_narrow_u64_to_u32(id-span.id);let p=sequence.rank<u32>(e.tree,slot,false);
 return Located{engine:Engine{..e,tree:p.tree,ids:f.index},slot:slot,offset:offset,rank:choose(slot==0,0,p.rank+offset+1),hint:f.hint};
}
// Identity-only access avoids computing a sequence rank when the caller only
// needs the stable slot and offset (visibility replay never observes rank).
fn identity_location(e:Engine,id:u64)->Located{
 let f=cursor.locate(e.ids,id,0);let slot=f.value;let span=e.spans.at_or(slot,nil());
 return Located{engine:Engine{..e,ids:f.index},slot:slot,offset:word_narrow_u64_to_u32(id-span.id),rank:0,hint:f.hint};
}
// Cached stable span handles survive later prefix-preserving refinement.
// Failed membership validation uses the original identity index.
fn fragment_location(e:Engine,id:u64,slot:u32)->Located{
 let s=e.spans.at_or(slot,nil());
 if slot!=0 && slot<e.spans.len() && refinement.covers(s.id,s.length,id){
  return Located{engine:e,slot:slot,offset:word_narrow_u64_to_u32(id-s.id),rank:0,hint:0};
 }
 return identity_location(e,id);
}
fn refined_location(e:Engine,id:u64,slot:u32)->Located{
 let r=fragment_location(e,id,slot);
 if r.offset==0{return r;}
 let next=r.engine.spans.len();let e=split(r.engine,r.slot,r.offset);
 return fragment_location(e,id,next);
}
fn split(e:Engine,slot:u32,offset:u32)->Engine{
 let s=e.spans.at_or(slot,nil());if slot==0 || offset==0 || offset>=s.length{return e;}
 let next=e.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next;let fresh=e.spans.len();
 let boundary=s.id+word_widen_u32_to_u64(offset);
 let a=Span{..s,length:offset,next_fragment:fresh};let b=Span{..s,interval_slot:e.ids.nodes.len(),id:boundary,left:boundary-1,length:s.length-offset,payload:s.payload+offset};
 let tree=sequence.set_extent<u32>(e.tree,slot,a.length,weight(a),0);
 let ids=partition.partition(e.ids,s.id,s.id+word_widen_u32_to_u64(s.length),boundary,slot,fresh,s.interval_slot);
 return Engine{..e,tree:sequence.insert_before<u32>(tree,next,fresh,b.length,weight(b),0),spans:e.spans.set(slot,a).push(b),ids:ids};
}
fn selected(e:Engine,position:u32)->Located{
 let p=sequence.seek<u32>(e.tree,position,true);
 return Located{engine:Engine{..e,tree:p.tree},slot:p.node,offset:p.offset,rank:0,hint:0};
}
fn anchor_selected(e:Engine,position:u32)->Located{
 let p=cross.seek<u32>(e.tree,position,1,0);
 return Located{engine:Engine{..e,tree:p.tree},slot:p.node,offset:p.offset,rank:p.rank,hint:0};
}
fn next_active(f:Find)->Find{
 let next=f.engine.tree.nodes.at_or(f.slot,sequence.nil<u32>(0)).next;
 return Find{engine:f.engine,slot:next};
}
fn scan_step(s:Scan,id:u64)->Scan{
 let destination=choose(s.scanning,s.destination,s.current);
 if s.current==0 || s.current==s.right{return Scan{..s,destination:destination,done:true};}
 let other=s.engine.spans.at_or(s.current,nil());let next=s.engine.tree.nodes.at_or(s.current,sequence.nil<u32>(0)).next;
 // Same immutable identity implies the same anchor rank. Hints remain
 // validated on use; skipping a query keeps its previous hint.
 let l=choose(other.left==s.left_id,Located{engine:s.engine,slot:0,offset:0,rank:s.left,hint:other.left_hint},hinted_lookup(s.engine,other.left,false,other.left_hint));let oleft=l.rank;let left_hint=l.hint;
 if oleft!=s.left{
  let current=s.current;let e=l.engine;
  let spans=choose(other.left_hint==left_hint,e.spans,e.spans.set(current,Span{..other,left_hint:left_hint}));
  return Scan{..s,engine:Engine{..e,spans:spans},current:next,destination:destination,done:oleft<s.left};
 }
 let r=choose(other.right==s.right_id,Located{engine:l.engine,slot:0,offset:0,rank:s.parent,hint:other.right_hint},hinted_lookup(l.engine,other.right,true,other.right_hint));let oright=r.rank;let right_hint=r.hint;
 let done=oleft<s.left || (oleft==s.left && oright==s.parent && id<other.id);
 let scanning=choose(oleft!=s.left,s.scanning,oright<s.parent);
 let current=s.current;let e=r.engine;
 let spans=choose(other.left_hint==left_hint && other.right_hint==right_hint,e.spans,e.spans.set(current,Span{..other,left_hint:left_hint,right_hint:right_hint}));
 return Scan{..s,engine:Engine{..e,spans:spans},current:next,destination:destination,scanning:scanning,done:done};
}
fn inserted(e:Engine,id:u64,position:u32,text:List<u32>)->Engine{
 let r=anchor_selected(e,choose(position==0,0,position-1));let slot=choose(position==0,0,r.slot);
 let leftrank=choose(slot==0,0,r.rank+r.offset+1);let left_hint=slot;
 let s=r.engine.spans.at_or(slot,nil());let left=choose(slot==0,0,s.id+word_widen_u32_to_u64(r.offset));
 let e=split(r.engine,slot,r.offset+1);
 let next=choose(slot==0,e.tree.first,e.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next);let bound=e.spans.len();
 let f=repeat_until(bound,Find{engine:e,slot:next},fn(f)=>f.slot==0 || f.engine.spans.at_or(f.slot,nil()).active,fn(i,f)=>next_active(f));
 let rightslot=f.slot;let right=f.engine.spans.at_or(rightslot,nil()).id;
 // The selected live span has weight equal to extent; splitting preserves
 // its total prefix. Cursor use validates the stable-slot hint before access.
 let r=lookup(f.engine,right,true);let parent=r.rank;let right_hint=r.hint;
 let current=choose(slot==0,r.engine.tree.first,r.engine.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next);let bound=r.engine.spans.len();
 let scan=repeat_until(bound,Scan{engine:r.engine,left:leftrank,right:rightslot,parent:parent,left_id:left,right_id:right,current:current,destination:current,scanning:false,done:false},fn(s)=>s.done,fn(i,s)=>scan_step(s,id));
 return committed(scan.engine,scan.destination,Anchors{id:id,left:left,right:right,left_hint:left_hint,right_hint:right_hint},text);
}
record Anchors{id:u64,left:u64,right:u64,left_hint:u32,right_hint:u32,}
fn committed(e:Engine,destination:u32,a:Anchors,text:List<u32>)->Engine{
 let length=length(text);let payload=e.payload.len();let fresh=e.spans.len();
 let span=Span{interval_slot:e.ids.nodes.len(),next_fragment:0,id:a.id,left:a.left,right:a.right,left_hint:a.left_hint,right_hint:a.right_hint,length:length,payload:payload,active:true,deletes:0,deleted:false};
 let data=foldl(text,e.payload,fn(value,data)=>data.push(value));
 let hint=e.ids.nodes.len();let ids=insertion.insert(e.ids,a.id,a.id+word_widen_u32_to_u64(length),fresh,e.insert_hint);
 return Engine{..e,insert_hint:hint,tree:sequence.insert_before<u32>(e.tree,destination,fresh,length,length,0),spans:e.spans.push(span),payload:data,ids:ids};
}

fn delete_step(d:Deleting)->Deleting{
 let r=selected(d.engine,d.position);let e=split(r.engine,r.slot,r.offset);let r=selected(e,d.position);
 let s=r.engine.spans.at_or(r.slot,nil());let take=choose(d.remaining<s.length,d.remaining,s.length);
 if r.slot==0 || take==0{let e=r.engine;return Deleting{..d,engine:Engine{..e,error:4},remaining:0};}
 let e=split(r.engine,r.slot,take);let s=e.spans.at_or(r.slot,nil());let changed=Span{..s,deletes:s.deletes+1,deleted:true};
 let target=Target{slot:r.slot,id:s.id,length:take,insert:false};
 return Deleting{..d,engine:Engine{..e,tree:sequence.set_weight<u32>(e.tree,r.slot,0),spans:e.spans.set(r.slot,changed)},targets:builder.push<Target>(d.targets,target),remaining:d.remaining-take};
}
fn toggle_step(t:Toggling,insert:Bool,on:Bool)->Toggling{
 let r=refined_location(t.engine,t.id,t.slot);
 let s=r.engine.spans.at_or(r.slot,nil());let take=choose(t.remaining<s.length,t.remaining,s.length);
 if r.slot==0 || take==0 || (!insert && !on && s.deletes==0){let e=r.engine;return Toggling{..t,engine:Engine{..e,error:4},remaining:0};}
 let e=split(r.engine,r.slot,take);let s=e.spans.at_or(r.slot,nil());
 let changed=Span{..s,active:choose(insert,on,s.active),deletes:choose(insert,s.deletes,choose(on,s.deletes+1,s.deletes-1))};
 // This engine maintains exact subtree measures. Metadata changes whose live
 // extent is unchanged therefore leave the measured sequence unchanged.
 let tree=choose(weight(s)==weight(changed),e.tree,sequence.set_weight<u32>(e.tree,r.slot,weight(changed)));
 return Toggling{engine:Engine{..e,tree:tree,spans:e.spans.set(r.slot,changed)},slot:changed.next_fragment,id:t.id+word_widen_u32_to_u64(take),remaining:t.remaining-take};
}
fn toggle(e:Engine,target:Target,on:Bool)->Engine{
 let result=repeat_until(target.length,Toggling{engine:e,slot:target.slot,id:target.id,remaining:target.length},fn(t)=>t.remaining==0 || t.engine.error!=0,fn(i,t)=>toggle_step(t,target.insert,on));
 return result.engine;
}
record TargetPass{walker:Walker,index:u32,end:u32,}
fn target_step(p:TargetPass,on:Bool)->TargetPass{
 let target=p.walker.applied.values.at_or(p.index,Target{slot:0,id:0,length:0,insert:false});let w=p.walker;
 return TargetPass{walker:Walker{..w,engine:toggle(w.engine,target,on)},index:p.index+1,end:p.end};
}
fn toggle_batch(w:Walker,index:u32,on:Bool)->Walker{
 let range=w.applied.ranges.at_or(index,ragged.nil());let count=range.end-range.start;
 let pass=repeat_until(count,TargetPass{walker:w,index:range.start,end:range.end},fn(p)=>p.index>=p.end,fn(i,p)=>target_step(p,on));return pass.walker;
}
fn retreat(w:Walker,r:causal.Range)->Walker{
 let x=repeat_until(r.end-r.start,Walking{walker:w,index:r.end},fn(x)=>x.index<=r.start || x.walker.engine.error!=0,fn(i,x)=>Walking{walker:toggle_batch(x.walker,x.index-2,false),index:x.index-1});return x.walker;
}
fn advance(w:Walker,r:causal.Range)->Walker{
 let x=repeat_until(r.end-r.start,Walking{walker:w,index:r.start},fn(x)=>x.index>=r.end || x.walker.engine.error!=0,fn(i,x)=>Walking{walker:toggle_batch(x.walker,x.index-1,true),index:x.index+1});return x.walker;
}
record RangePass{walker:Walker,ranges:Buffer<causal.Range>,index:u32,}
fn removed_step(x:RangePass)->RangePass{
 let range=x.ranges.at_or(x.index,causal.Range{start:0,end:0});
 return RangePass{..x,walker:retreat(x.walker,range),index:x.index+1};
}
fn added_step(x:RangePass)->RangePass{
 let range=x.ranges.at_or(x.index-1,causal.Range{start:0,end:0});
 return RangePass{..x,walker:advance(x.walker,range),index:x.index-1};
}
record PreparedParents{walker:Walker,parents:List<u32>,}
fn resolved(w:Walker,parents:List<u64>)->PreparedParents{
 var ends:Map<u64,u32>=w.ends;var values:Buffer<u32>=Buffer.empty();
 for p in parents{values=values.push(ends.get_or(p,0));ends=ends;}
 return PreparedParents{walker:Walker{..w,ends:ends},parents:values.freeze()};
}
fn prepare_resolved(w:Walker,parents:List<u32>,follows:Bool)->Walker{
 if follows{return w;}
 let ends=w.ends;let left:List<u32>=choose(w.last==0,[],[ends.get_or(w.last,0)]);
 let d=causal.difference(w.graph,left,parents);let valid=d.valid;
 let removed=d.removed;let added=d.added;
 let w=Walker{..w,graph:d.graph,ends:ends};if !valid{return Walker{..w,error:4};}
 let count=removed.len();
 let gone=repeat_until(count,RangePass{walker:w,ranges:removed,index:0},fn(x)=>x.index>=x.ranges.len() || x.walker.engine.error!=0,fn(i,x)=>removed_step(x));
 let count=added.len();
 let brought=repeat_until(count,RangePass{walker:gone.walker,ranges:added,index:count},fn(x)=>x.index==0 || x.walker.engine.error!=0,fn(i,x)=>added_step(x));
 let w=brought.walker;let graph=causal.recycled(w.graph,gone.ranges,brought.ranges);
 return Walker{..w,graph:graph};
}
fn prepare(w:Walker,parents:List<u64>)->Walker{
 let follows=(w.last==0 && length(parents)==0) || (w.last!=0 && length(parents)==1 && parents.at_or(0,0)==w.last);
 if follows{return w;}let r=resolved(w,parents);return prepare_resolved(r.walker,r.parents,false);
}
fn apply(w:Walker,c:batches.Change)->Walker{
 if w.error!=0 || w.engine.error!=0{return w;}
 let codes=foldl(c.text,true,fn(value,ok)=>ok && value<1114112 && !(value>=55296 && value<57344));
 if !batches.valid(c) || !codes{return Walker{..w,error:4};}
 let slot=w.applied.ranges.len()+1;let end=c.id+batches.width(c);let identities=fused_intervals.insert(w.identities,c.id,end,slot);
 let w=Walker{..w,identities:identities};if !w.identities.valid{return Walker{..w,error:4};}
 let follows=(w.last==0 && length(c.parents)==0) || (w.last!=0 && length(c.parents)==1 && c.parents.at_or(0,0)==w.last);
 let r=resolved(w,c.parents);let local_parents=r.parents;let w=prepare_resolved(r.walker,local_parents,follows);if w.error!=0 || w.engine.error!=0{return w;}
 let root=w.engine.tree.blocks.at_or(w.engine.tree.root,sequence.empty_block());
 if c.position>root.live || c.remove>root.live-c.position{return Walker{..w,error:4};}
 let d=repeat_until(c.remove,Deleting{engine:w.engine,targets:builder.begin<Target>(w.applied),remaining:c.remove,position:c.position},fn(d)=>d.remaining==0 || d.engine.error!=0,fn(i,d)=>delete_step(d));
 let insertid=c.id+word_widen_u32_to_u64(c.remove);let count=length(c.text);
 let e=choose(count==0,d.engine,inserted(d.engine,insertid,c.position,c.text));
 let targets=choose(count==0,d.targets,builder.push<Target>(d.targets,Target{slot:e.spans.len()-1,id:insertid,length:count,insert:true}));
 let ends=w.ends;
 return Walker{..w,engine:e,graph:causal.append(w.graph,local_parents),ends:ends.set(end-1,slot),applied:builder.finish<Target>(targets),last:end-1};
}
fn output_value(o:Output,index:u32)->Output{let value=o.engine.payload.at_or(index,0);return Output{..o,values:o.values.push(value)};}
fn output_span(o:Output)->Output{
 let s=o.engine.spans.at_or(o.slot,nil());let next=o.engine.tree.nodes.at_or(o.slot,sequence.nil<u32>(0)).next;
 let count=choose(s.deleted,0,s.length);
 let out=repeat_until(count,o,fn(o)=>false,fn(i,o)=>output_value(o,s.payload+i));
 return Output{..out,slot:next};
}
fn walked(changes:List<batches.Change>)->Result<List<u32>,reference.Error>{
 var w:Walker=empty();for c in changes{w=apply(w,c);}
 if w.error!=0 || w.engine.error!=0 || !w.graph.valid || !w.engine.ids.valid{return Err(reference.Error.InvalidOperation);}
 let first=w.engine.tree.first;let bound=w.engine.spans.len();
 let out=repeat_until(bound,Output{engine:w.engine,slot:first,values:Buffer.empty()},fn(o)=>o.slot==0,fn(i,o)=>output_span(o));return Ok(out.values.freeze());
}
fn eligible(changes:List<batches.Change>)->Bool{
 var ends:Map<u64,Bool>=Map.empty();var result:Bool=true;
 for c in changes{
  result=result && batches.valid(c);
  for p in c.parents{result=result && ends.get_or(p,false);ends=ends;}
  ends=ends.set(c.id+batches.width(c)-1,true);
 }
 return result;
}
fn completed(result:Result<List<u32>,reference.Error>,changes:List<batches.Change>)->Result<List<u32>,reference.Error>{
 return match result{Ok(text)=>Ok(text),Err(error)=>batches.materialize(changes),};
}
fn materialize(changes:List<batches.Change>)->Result<List<u32>,reference.Error>{
 if batches.is_linear(changes){return batches.linear(changes);}
 return completed(walked(changes),changes);
}
