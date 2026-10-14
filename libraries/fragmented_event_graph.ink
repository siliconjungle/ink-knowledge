module ink.knowledge.fragmented_event_graph;
import "batched_event_graph.ink" as batches;
import "interval_index.ink" as intervals;
import "interval_fused.ink" as fused;
import "span_cursor_event_graph.ink" as endpoints;
import "projected_event_graph.ink" as projected;
import "text_crdts.ink" as reference;
// Ordinary source adapter. Split only at referenced operation frontiers, so
// complete scalar expansion retains IDs, parents, positions and codepoints.
record Built{index:intervals.Index,cuts:Map<u32,List<u32>>,next:u32,valid:Bool,}
fn prepare(b:Built,c:batches.Change)->Built{
 if !b.valid || !batches.valid(c){return Built{..b,valid:false};}
 var b:Built=b;
 for parent in c.parents{
  let found=intervals.locate(b.index,parent);let slot=found.value;
  let offset=word_narrow_u64_to_u32(parent-found.start+1);
  let values=b.cuts.get_or(slot,[]);
  b=Built{..b,index:found.index,cuts:b.cuts.set(slot,values.concat([offset])),valid:b.valid && slot!=0};
 }
 let index=fused.insert(b.index,c.id,c.id+batches.width(c),b.next);let valid=index.valid;
 return Built{..b,index:index,next:b.next+1,valid:b.valid && valid};
}
record Parts{source:batches.Change,values:Buffer<batches.Change>,offset:u32,}
fn piece(p:Parts,end:u32)->Parts{
 if end<=p.offset{return p;}
 let remove_end=choose(end<p.source.remove,end,p.source.remove);
 let removed=choose(p.offset<remove_end,remove_end-p.offset,0);
 let first=choose(p.offset>p.source.remove,p.offset-p.source.remove,0);
 let last=choose(end>p.source.remove,end-p.source.remove,0);
 let c=batches.Change{id:p.source.id+word_widen_u32_to_u64(p.offset),parents:choose(p.offset==0,p.source.parents,[p.source.id+word_widen_u32_to_u64(p.offset)-1]),position:p.source.position+first,remove:removed,text:p.source.text.drop(first).take(last-first)};
 return Parts{..p,values:p.values.push(c),offset:end};
}
fn built(changes:List<batches.Change>)->Built{
 var b:Built=Built{index:intervals.empty(),cuts:Map.empty(),next:1,valid:true};
 for c in changes{b=prepare(b,c);}
 return b;
}
record Fragments{changes:List<batches.Change>,valid:Bool,}
fn fragmented(changes:List<batches.Change>)->Fragments{
 let b=built(changes);
 if !b.valid{return Fragments{changes:changes,valid:false};}
 var cuts:Map<u32,List<u32>>=b.cuts;var values:Buffer<batches.Change>=Buffer.empty();var index:u32=1;
 for c in changes{
  let ends=cuts.get_or(index,[]).concat([word_narrow_u64_to_u32(batches.width(c))]).sort();
  let p=foldl(ends,Parts{source:c,values:values,offset:0},fn(end,p)=>piece(p,end));
  values=p.values;cuts=cuts;index=index+1;
 }
 return Fragments{changes:values.freeze(),valid:true};
}
fn materialize(changes:List<batches.Change>)->Result<List<u32>,reference.Error>{
 if endpoints.eligible(changes){return projected.materialize(changes);}
 let parts=fragmented(changes);
 return choose(parts.valid,projected.materialize(parts.changes),batches.materialize(changes));
}
