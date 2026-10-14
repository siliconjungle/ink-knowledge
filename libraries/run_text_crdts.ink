module ink.knowledge.run_text_crdts;
import "text_crdts.ink" as reference;
import "weighted_sequence.ink" as sequence;
import "interval_index.ink" as intervals;
record Span{id:u64,left:u64,right:u64,stamp:u64,step:u64,length:u32,payload:u32,deleted:Bool,}
record Engine{tree:sequence.Tree<u32>,spans:Buffer<Span>,payload:Buffer<u32>,ids:intervals.Index,pending:Map<u64,Bool>,error:u32,}
record Located{engine:Engine,slot:u32,offset:u32,rank:u32,}
record Scan{engine:Engine,left:u32,right:u32,parent:u32,current:u32,destination:u32,scanning:Bool,done:Bool,}
record Output{engine:Engine,slot:u32,atoms:Buffer<reference.Atom>,}
record Local{engine:Engine,counter:u64,stamp:u64,}
record Edit{position:u32,remove:u32,text:List<u32>,}
fn nil()->Span{return Span{id:0,left:0,right:0,stamp:0,step:0,length:0,payload:0,deleted:true};}
fn empty()->Engine{return Engine{tree:sequence.empty<u32>(0),spans:buffer([nil()]),payload:Buffer.empty(),ids:intervals.empty(),pending:Map.empty(),error:0};}
fn lookup(e:Engine,id:u64,right:Bool)->Located{
 if id==0{let n=e.tree.nodes.at_or(e.tree.root,sequence.nil<u32>(0));let rank=choose(right,n.size+1,0);return Located{engine:e,slot:0,offset:0,rank:rank};}
 let f=intervals.locate(e.ids,id);let slot=f.value;let s=e.spans.at_or(slot,nil());let offset=word_narrow_u64_to_u32(id-s.id);
 let p=sequence.rank<u32>(e.tree,slot,false);let rank=choose(slot==0,0,p.rank+offset+1);
 return Located{engine:Engine{tree:p.tree,spans:e.spans,payload:e.payload,ids:f.index,pending:e.pending,error:e.error},slot:slot,offset:offset,rank:rank};
}
fn decoded(e:Engine,slot:u32,offset:u32)->reference.Atom{
 let s=e.spans.at_or(slot,nil());let id=s.id+word_widen_u32_to_u64(offset);
 return reference.Atom{id:id,left:choose(offset==0,s.left,id-1),right:s.right,stamp:s.stamp+s.step*word_widen_u32_to_u64(offset),value:e.payload.at_or(s.payload+offset,0),deleted:s.deleted};
}
record Decoded{engine:Engine,atom:reference.Atom,}
fn atom(e:Engine,slot:u32,offset:u32)->Decoded{
 let s=e.spans.at_or(slot,nil());let id=s.id+word_widen_u32_to_u64(offset);
 let a=reference.Atom{id:id,left:choose(offset==0,s.left,id-1),right:s.right,stamp:s.stamp+s.step*word_widen_u32_to_u64(offset),value:e.payload.at_or(s.payload+offset,0),deleted:s.deleted};
 return Decoded{engine:e,atom:a};
}
fn split(e:Engine,slot:u32,offset:u32)->Engine{
 let s=e.spans.at_or(slot,nil());if slot==0 || offset==0 || offset>=s.length{return e;}
 let next=e.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next;let fresh=e.spans.len();let boundary=s.id+word_widen_u32_to_u64(offset);
 let a=Span{id:s.id,left:s.left,right:s.right,stamp:s.stamp,step:s.step,length:offset,payload:s.payload,deleted:s.deleted};
 let b=Span{id:boundary,left:boundary-1,right:s.right,stamp:s.stamp+s.step*word_widen_u32_to_u64(offset),step:s.step,length:s.length-offset,payload:s.payload+offset,deleted:s.deleted};
 let tree=sequence.set_extent<u32>(e.tree,slot,a.length,choose(a.deleted,0,a.length));
 let ids=intervals.insert(intervals.changed_end(e.ids,s.id,boundary),boundary,s.id+word_widen_u32_to_u64(s.length),fresh);
 return Engine{tree:sequence.insert_before<u32>(tree,next,fresh,b.length,choose(b.deleted,0,b.length)),spans:e.spans.set(slot,a).push(b),payload:e.payload,ids:ids,pending:e.pending,error:e.error};
}
fn parent(e:Engine,a:reference.Atom,mode:u32)->Located{
 let r=lookup(e,a.right,true);
 if mode!=3 || r.slot==0{return r;}
 let got=atom(r.engine,r.slot,r.offset);let keep=got.atom.left==a.left;
 return choose(keep,lookup(got.engine,a.right,true),lookup(got.engine,0,true));
}
fn scan_step(s:Scan,a:reference.Atom,mode:u32)->Scan{
 let destination=choose(s.scanning,s.destination,s.current);
 if s.current==0 || (mode!=2 && s.current==s.right){return Scan{engine:s.engine,left:s.left,right:s.right,parent:s.parent,current:s.current,destination:destination,scanning:s.scanning,done:true};}
 let got=atom(s.engine,s.current,0);let other=got.atom;let next=got.engine.tree.nodes.at_or(s.current,sequence.nil<u32>(0)).next;
 let l=lookup(got.engine,other.left,false);let oleft=l.rank;let r=parent(l.engine,other,mode);let oright=r.rank;
 let done=choose(mode==2,a.stamp>other.stamp || oleft<s.left || (oleft==s.left && a.stamp==other.stamp && reference.actor(a.id)>reference.actor(other.id)),
  oleft<s.left || (oleft==s.left && oright==s.parent && reference.actor(a.id)<reference.actor(other.id)));
 let scanning=choose(mode==2,false,choose(oleft!=s.left,s.scanning,choose(mode==1,reference.actor(a.id)<reference.actor(other.id),oright<s.parent)));
 return Scan{engine:r.engine,left:s.left,right:s.right,parent:s.parent,current:next,destination:destination,scanning:scanning,done:done};
}
fn inserted(e:Engine,a:reference.Atom,destination:u32,mode:u32)->Engine{
 let before=e.tree.nodes.at_or(destination,sequence.nil<u32>(0));let previous=choose(destination==0,e.tree.last,before.previous);
 let s=e.spans.at_or(previous,nil());let length=word_widen_u32_to_u64(s.length);let deleted=a.deleted || e.pending.get_or(a.id,false);
 let delta=choose(s.length==1,a.stamp-s.stamp,s.step);
 let merged=previous!=0 && s.id+length==a.id && a.left==a.id-1 && a.right==s.right && s.deleted==deleted && s.payload+s.length==e.payload.len() &&
  a.stamp==s.stamp+delta*length && (mode!=2 || (delta==1 && a.stamp>s.stamp));
 let payload=e.payload.push(a.value);
 if merged{
  let replacement=Span{id:s.id,left:s.left,right:s.right,stamp:s.stamp,step:delta,length:s.length+1,payload:s.payload,deleted:s.deleted};
  return Engine{tree:sequence.set_extent<u32>(e.tree,previous,replacement.length,choose(deleted,0,replacement.length)),spans:e.spans.set(previous,replacement),payload:payload,
   ids:intervals.changed_end(e.ids,s.id,a.id+1),pending:e.pending,error:e.error};
 }
 let slot=e.spans.len();let s=Span{id:a.id,left:a.left,right:a.right,stamp:a.stamp,step:0,length:1,payload:payload.len()-1,deleted:deleted};
 return Engine{tree:sequence.insert_before<u32>(e.tree,destination,slot,1,choose(deleted,0,1)),spans:e.spans.push(s),payload:payload,ids:intervals.insert(e.ids,a.id,a.id+1,slot),pending:e.pending,error:e.error};
}
fn receive(e:Engine,op:reference.Operation,mode:u32)->Engine{
 if e.error!=0{return e;}
 if mode>3{return Engine{tree:e.tree,spans:e.spans,payload:e.payload,ids:e.ids,pending:e.pending,error:3};}
 if !op.insert{
  let r=lookup(e,op.target,false);let e=split(r.engine,r.slot,r.offset);let r=lookup(e,op.target,false);let e=split(r.engine,r.slot,1);
  let s=e.spans.at_or(r.slot,nil());let value=Span{id:s.id,left:s.left,right:s.right,stamp:s.stamp,step:s.step,length:s.length,payload:s.payload,deleted:true};
  return Engine{tree:sequence.set_weight<u32>(e.tree,r.slot,0),spans:choose(r.slot==0,e.spans,e.spans.set(r.slot,value)),payload:e.payload,ids:e.ids,pending:e.pending.set(op.target,true),error:e.error};
 }
 let a=op.atom;
 if !reference.valid_insertion(a){return Engine{tree:e.tree,spans:e.spans,payload:e.payload,ids:e.ids,pending:e.pending,error:4};}
 let found=lookup(e,a.id,false);
 if found.slot!=0{let old=atom(found.engine,found.slot,found.offset);let error:u32=choose(reference.same_insertion(a,old.atom),0,2);return Engine{tree:old.engine.tree,spans:old.engine.spans,payload:old.engine.payload,ids:old.engine.ids,pending:old.engine.pending,error:error};}
 let prev=lookup(found.engine,choose((a.id & 4294967295)>1,a.id-1,0),false);
 if (a.id & 4294967295)>1 && prev.slot==0{return Engine{tree:prev.engine.tree,spans:prev.engine.spans,payload:prev.engine.payload,ids:prev.engine.ids,pending:prev.engine.pending,error:1};}
 let l=lookup(prev.engine,a.left,false);let left=l.rank;let missing=a.left!=0 && l.slot==0;let e=split(l.engine,l.slot,l.offset+1);
 let r=lookup(e,a.right,true);let missing=missing || (mode!=2 && a.right!=0 && r.slot==0);let rightpos=r.rank;
 let e=choose(mode==2,r.engine,split(r.engine,r.slot,r.offset));
 if missing{return Engine{tree:e.tree,spans:e.spans,payload:e.payload,ids:e.ids,pending:e.pending,error:1};}
 if mode!=2 && left>=rightpos{return Engine{tree:e.tree,spans:e.spans,payload:e.payload,ids:e.ids,pending:e.pending,error:4};}
 let r=lookup(e,a.right,true);let right=r.slot;let p=parent(r.engine,a,mode);let target=p.rank;let l=lookup(p.engine,a.left,false);
 let current=choose(l.slot==0,l.engine.tree.first,l.engine.tree.nodes.at_or(l.slot,sequence.nil<u32>(0)).next);let bound=l.engine.spans.len();
 let s=repeat_until(bound,Scan{engine:l.engine,left:left,right:right,parent:target,current:current,destination:current,scanning:false,done:false},fn(s)=>s.done,fn(i)=>fn(s)=>scan_step(s,a,mode));
 return inserted(s.engine,a,s.destination,mode);
}
fn output_span(o:Output)->Output{
 let s=o.engine.spans.at_or(o.slot,nil());let next=o.engine.tree.nodes.at_or(o.slot,sequence.nil<u32>(0)).next;
 let result=repeat_until(s.length,Output{engine:o.engine,slot:o.slot,atoms:o.atoms},fn(o)=>false,fn(i)=>fn(o)=>output_atom(o,i));
 return Output{engine:result.engine,slot:next,atoms:result.atoms};
}
fn output_atom(o:Output,offset:u32)->Output{let got=atom(o.engine,o.slot,offset);return Output{engine:got.engine,slot:o.slot,atoms:o.atoms.push(got.atom)};}
fn finish(e:Engine)->Result<List<reference.Atom>,reference.Error>{
 if e.error==1{return Err(reference.Error.MissingDependency);}if e.error==2{return Err(reference.Error.ConflictingIdentity);}if e.error==3{return Err(reference.Error.InvalidMode);}if e.error==5{return Err(reference.Error.InvalidPosition);}if e.error!=0 || !e.ids.valid{return Err(reference.Error.InvalidOperation);}
 let first=e.tree.first;let bound=e.spans.len();let o=repeat_until(bound,Output{engine:e,slot:first,atoms:Buffer.empty()},fn(o)=>o.slot==0,fn(i)=>fn(o)=>output_span(o));return Ok(o.atoms.freeze());
}
fn replay(ops:List<reference.Operation>,mode:u32)->Result<List<reference.Atom>,reference.Error>{var e:Engine=empty();for op in ops{e=receive(e,op,mode);}return finish(e);}
fn selected(e:Engine,position:u32)->Located{
 let p=sequence.seek<u32>(e.tree,position,true);
 return Located{engine:Engine{tree:p.tree,spans:e.spans,payload:e.payload,ids:e.ids,pending:e.pending,error:e.error},slot:p.node,offset:p.offset,rank:0};
}
fn local_insert(s:Local,position:u32,value:u32,mode:u32)->Local{
 if s.engine.error!=0{return s;}
 let root=s.engine.tree.nodes.at_or(s.engine.tree.root,sequence.nil<u32>(0));
 if position>root.live{return Local{engine:Engine{tree:s.engine.tree,spans:s.engine.spans,payload:s.engine.payload,ids:s.engine.ids,pending:s.engine.pending,error:5},counter:s.counter,stamp:s.stamp};}
 let r=selected(s.engine,choose((mode==0 || mode==3) && position>0,position-1,position));
 let slot=choose((mode==0 || mode==3) && position==0,0,r.slot);
 let span=r.engine.spans.at_or(slot,nil());let node=r.engine.tree.nodes.at_or(slot,sequence.nil<u32>(0));
 let current=span.id+word_widen_u32_to_u64(r.offset);
 let previous=choose(slot==0,r.engine.tree.last,node.previous);let before=r.engine.spans.at_or(previous,nil());
 let left=choose(mode==0 || mode==3,choose(slot==0,0,current),choose(slot==0,choose(previous==0,0,before.id+word_widen_u32_to_u64(before.length)-1),choose(r.offset==0,choose(previous==0,0,before.id+word_widen_u32_to_u64(before.length)-1),current-1)));
 let next=choose(slot==0,r.engine.tree.first,node.next);let after=r.engine.spans.at_or(next,nil());
 let right=choose(mode==0 || mode==3,choose(slot==0,after.id,choose(r.offset+1<span.length,current+1,after.id)),choose(slot==0,0,current));
 let counter=s.counter+1;let stamp=s.stamp+1;
 let a=reference.Atom{id:reference.identity(1,counter),left:left,right:right,stamp:stamp,value:value,deleted:false};
 return Local{engine:receive(r.engine,reference.Operation{insert:true,atom:a,target:0},mode),counter:counter,stamp:stamp};
}
fn local_delete(s:Local,position:u32,mode:u32)->Local{
 if s.engine.error!=0{return s;}
 let root=s.engine.tree.nodes.at_or(s.engine.tree.root,sequence.nil<u32>(0));
 if position>=root.live{return Local{engine:Engine{tree:s.engine.tree,spans:s.engine.spans,payload:s.engine.payload,ids:s.engine.ids,pending:s.engine.pending,error:5},counter:s.counter,stamp:s.stamp};}
 let r=selected(s.engine,position);let span=r.engine.spans.at_or(r.slot,nil());let id=span.id+word_widen_u32_to_u64(r.offset);
 return Local{engine:receive(r.engine,reference.Operation{insert:false,atom:reference.empty_atom(),target:id},mode),counter:s.counter,stamp:s.stamp+1};
}
fn local_engine(edits:List<Edit>,mode:u32)->Engine{
 var s:Local=Local{engine:empty(),counter:0,stamp:0};
 for edit in edits{s=edit_one(s,edit,mode);}return s.engine;
}
fn local(edits:List<Edit>,mode:u32)->Result<List<reference.Atom>,reference.Error>{return finish(local_engine(edits,mode));}
record Editing{local:Local,position:u32,}
fn edit_step(e:Editing,value:u32,mode:u32)->Editing{return Editing{local:local_insert_fast(e.local,e.position,value,mode),position:e.position+1};}
fn edit_one(s:Local,edit:Edit,mode:u32)->Local{
 let remove=edit.remove;let position=edit.position;let text=edit.text;
 let s=repeat_until(remove,s,fn(s)=>s.engine.error!=0,fn(i)=>fn(s)=>local_delete(s,position,mode));
 let e=foldl(text,Editing{local:s,position:position},fn(value)=>fn(e)=>edit_step(e,value,mode));return e.local;
}

record TextOutput{engine:Engine,slot:u32,values:Buffer<u32>,}
fn text_atom(o:TextOutput,offset:u32)->TextOutput{let s=o.engine.spans.at_or(o.slot,nil());let value=o.engine.payload.at_or(s.payload+offset,0);return TextOutput{engine:o.engine,slot:o.slot,values:o.values.push(value)};}
fn text_span(o:TextOutput)->TextOutput{
 let s=o.engine.spans.at_or(o.slot,nil());let next=o.engine.tree.nodes.at_or(o.slot,sequence.nil<u32>(0)).next;
 let count=choose(s.deleted,0,s.length);let r=repeat_until(count,o,fn(o)=>false,fn(i)=>fn(o)=>text_atom(o,i));
 return TextOutput{engine:r.engine,slot:next,values:r.values};
}
fn visible(e:Engine)->Result<List<u32>,reference.Error>{
 if e.error==1{return Err(reference.Error.MissingDependency);}if e.error==2{return Err(reference.Error.ConflictingIdentity);}if e.error==3{return Err(reference.Error.InvalidMode);}if e.error==5{return Err(reference.Error.InvalidPosition);}if e.error!=0 || !e.ids.valid{return Err(reference.Error.InvalidOperation);}
 let first=e.tree.first;let bound=e.spans.len();let o=repeat_until(bound,TextOutput{engine:e,slot:first,values:Buffer.empty()},fn(o)=>o.slot==0,fn(i)=>fn(o)=>text_span(o));return Ok(o.values.freeze());
}
fn local_text(edits:List<Edit>,mode:u32)->Result<List<u32>,reference.Error>{return visible(local_engine(edits,mode));}

// Generated local edits all follow the prior local state. Their two anchors
// delimit adjacent raw positions, so integration cannot scan concurrent items.
fn local_insert_fast(s:Local,position:u32,value:u32,mode:u32)->Local{
 if s.engine.error!=0{return s;}
 let root=s.engine.tree.nodes.at_or(s.engine.tree.root,sequence.nil<u32>(0));
 if position>root.live{return Local{engine:Engine{tree:s.engine.tree,spans:s.engine.spans,payload:s.engine.payload,ids:s.engine.ids,pending:s.engine.pending,error:5},counter:s.counter,stamp:s.stamp};}
 let r=selected(s.engine,choose((mode==0 || mode==3) && position>0,position-1,position));
 let slot=choose((mode==0 || mode==3) && position==0,0,r.slot);
 let span=r.engine.spans.at_or(slot,nil());let node=r.engine.tree.nodes.at_or(slot,sequence.nil<u32>(0));
 let current=span.id+word_widen_u32_to_u64(r.offset);
 let previous=choose(slot==0,r.engine.tree.last,node.previous);let before=r.engine.spans.at_or(previous,nil());
 let left=choose(mode==0 || mode==3,choose(slot==0,0,current),choose(slot==0,choose(previous==0,0,before.id+word_widen_u32_to_u64(before.length)-1),choose(r.offset==0,choose(previous==0,0,before.id+word_widen_u32_to_u64(before.length)-1),current-1)));
 let next=choose(slot==0,r.engine.tree.first,node.next);let after=r.engine.spans.at_or(next,nil());
 let right=choose(mode==0 || mode==3,choose(slot==0,after.id,choose(r.offset+1<span.length,current+1,after.id)),choose(slot==0,0,current));
 let counter=s.counter+1;let stamp=s.stamp+1;
 let a=reference.Atom{id:reference.identity(1,counter),left:left,right:right,stamp:stamp,value:value,deleted:false};
 if mode>3{return Local{engine:Engine{tree:r.engine.tree,spans:r.engine.spans,payload:r.engine.payload,ids:r.engine.ids,pending:r.engine.pending,error:3},counter:counter,stamp:stamp};}
 if !reference.valid_insertion(a){return Local{engine:Engine{tree:r.engine.tree,spans:r.engine.spans,payload:r.engine.payload,ids:r.engine.ids,pending:r.engine.pending,error:4},counter:counter,stamp:stamp};}
 let fresh=r.engine.spans.len();
 let e=choose(mode==0 || mode==3,split(r.engine,slot,r.offset+1),split(r.engine,slot,r.offset));
 let destination=choose(mode==0 || mode==3,choose(slot==0,e.tree.first,e.tree.nodes.at_or(slot,sequence.nil<u32>(0)).next),choose(slot==0,0,choose(r.offset==0,slot,fresh)));
 return Local{engine:inserted(e,a,destination,mode),counter:counter,stamp:stamp};
}
