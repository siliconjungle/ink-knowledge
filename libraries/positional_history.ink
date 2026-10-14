module ink.knowledge.positional_history;
import "gap_sequence.ink" as sequence;
record Edit{position:u32,remove:u32,text:List<u32>,}
record Run{position:u32,remove:u32,inserted:u32,payload:u32,events:u32,forward:Bool,}
record Snapshot{text:List<u32>,history:List<Run>,payload:List<u32>,}
record Builder{sequence:sequence.Gap<u32>,runs:Buffer<Run>,payload:Buffer<u32>,}
record Written{sequence:sequence.Gap<u32>,payload:Buffer<u32>,}
record EditMeta{position:u32,remove:u32,inserted:u32,payload:u32,}
fn empty_run()->Run{return Run{position:0,remove:0,inserted:0,payload:0,events:0,forward:true};}
fn append_history(b:Builder,e:EditMeta)->Builder {
 let n=e.inserted;let at=e.payload;
 if e.remove==0 && n==0 {return b;}
 let last=b.runs.len()-1;
 let previous=b.runs.at_or(last,empty_run());
 let reverse=previous.events==1 && previous.inserted==1 && previous.remove==0 &&
  e.remove==0 && n==1 && e.position==previous.position;
 let deletions=previous.events!=0 && previous.inserted==0 && n==0 && e.position==previous.position;
 let merge=previous.events!=0 && previous.remove==0 && e.remove==0 &&
  ((previous.forward && e.position==previous.position+previous.inserted) ||
   (!previous.forward && n==1 && e.position==previous.position));
 let previous=Run{position:previous.position,remove:previous.remove+e.remove,inserted:previous.inserted+n,
  payload:previous.payload,events:previous.events+n+e.remove,forward:previous.forward && !reverse};
 let next=Run{position:e.position,remove:e.remove,inserted:n,payload:at,events:n+e.remove,forward:true};
 let runs=choose(merge || reverse || deletions,b.runs.set(last,previous),b.runs.push(next));
 return Builder{sequence:b.sequence,runs:runs,payload:b.payload};
}
fn write(value:u32,b:Written)->Written {
 return Written{sequence:sequence.inserted<u32>(b.sequence,value),payload:b.payload.push(value)};
}
fn build(edits:List<Edit>)->Snapshot {
 var b:Builder=Builder{sequence:sequence.empty<u32>(0),runs:Buffer.empty(),payload:Buffer.empty()};
 for edit in edits {
  // Total sequence semantics clip positions/ranges. The log records the
  // clipped edit too, so every decoded future prefix reproduces the text.
  let total=b.sequence.data.len()-b.sequence.end+b.sequence.start;
  let position=choose(edit.position>total,total,edit.position);
  let remove=choose(edit.remove>total-position,total-position,edit.remove);
  let inserted=length(edit.text);let payload=b.payload.len();
  let moved=sequence.moved<u32>(b.sequence,position);
  let removed=sequence.erased<u32>(moved,remove);
  let changed=foldl(edit.text,Written{sequence:removed,payload:b.payload},fn(value)=>fn(g)=>write(value,g));
  b=append_history(Builder{sequence:changed.sequence,runs:b.runs,payload:changed.payload},EditMeta{position:position,remove:remove,inserted:inserted,payload:payload});
 }
 return Snapshot{text:sequence.freeze<u32>(b.sequence),history:b.runs.freeze(),payload:b.payload.freeze()};
}
