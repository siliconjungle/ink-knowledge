module ink.knowledge.indexed_text_crdts;
import "text_crdts.ink" as reference;
import "measured_sequence.ink" as sequence;
record Engine { tree:sequence.Tree<reference.Atom>, ids:Map<u64,u32>, deleted:Map<u64,Bool>, error:u32, }
record Located { engine:Engine, rank:u32, }
record Scan { engine:Engine, left:u32, right:u32, parent:u32, current:u32, destination:u32, scanning:Bool, done:Bool, }
record Edit { position:u32, remove:u32, text:List<u32>, }
record Local { engine:Engine, counter:u64, stamp:u64, }
fn empty()->Engine {return Engine{tree:sequence.empty<reference.Atom>(reference.empty_atom()),ids:Map.empty(),deleted:Map.empty(),error:0};}
fn located(e:Engine,slot:u32,right:Bool)->Located {
 if slot==0 {let rank=choose(right,e.tree.nodes.len(),0);return Located{engine:e,rank:rank};}
 let r=sequence.rank<reference.Atom>(e.tree,slot,false);
 return Located{engine:Engine{tree:r.tree,ids:e.ids,deleted:e.deleted,error:e.error},rank:r.rank+1};
}
fn right_parent(e:Engine,atom:reference.Atom,mode:u32)->Located {
 let slot=e.ids.get_or(atom.right,0);
 let node=e.tree.nodes.at_or(slot,sequence.nil<reference.Atom>(reference.empty_atom()));
 let slot=choose(mode==3 && (slot==0 || node.value.left!=atom.left),0,slot);
 return located(e,slot,true);
}
fn scan_step(s:Scan,atom:reference.Atom,mode:u32)->Scan {
 let destination=choose(s.scanning,s.destination,s.current);
 if s.current==0 || (mode!=2 && s.current==s.right) {
  return Scan{engine:s.engine,left:s.left,right:s.right,parent:s.parent,current:s.current,destination:destination,scanning:s.scanning,done:true};
 }
 let node=s.engine.tree.nodes.at_or(s.current,sequence.nil<reference.Atom>(reference.empty_atom()));
 let other=node.value;let next=node.next;let leftslot=s.engine.ids.get_or(other.left,0);
 let left=located(s.engine,leftslot,false);let oleft=left.rank;
 let right=right_parent(left.engine,other,mode);let oright=right.rank;
 let done=choose(mode==2,atom.stamp>other.stamp || oleft<s.left ||
  (oleft==s.left && atom.stamp==other.stamp && reference.actor(atom.id)>reference.actor(other.id)),
  oleft<s.left || (oleft==s.left && oright==s.parent && reference.actor(atom.id)<reference.actor(other.id)));
 let scanning=choose(mode==2,false,choose(oleft!=s.left,s.scanning,
  choose(mode==1,reference.actor(atom.id)<reference.actor(other.id),oright<s.parent)));
 return Scan{engine:right.engine,left:s.left,right:s.right,parent:s.parent,current:next,
  destination:destination,scanning:scanning,done:done};
}
fn receive(e:Engine,op:reference.Operation,mode:u32)->Engine {
 return receive_sequenced(e,op,mode,true);
}
// Event graphs sequence all events, including deletes. Their insertion IDs may
// have gaps; the graph library independently checks that full event sequence.
fn receive_event(e:Engine,op:reference.Operation,mode:u32)->Engine {
 return receive_sequenced(e,op,mode,false);
}
fn receive_sequenced(e:Engine,op:reference.Operation,mode:u32,insertion_sequence:Bool)->Engine {
 if e.error!=0 {return e;}
 if mode>3 {return Engine{tree:e.tree,ids:e.ids,deleted:e.deleted,error:3};}
 if !op.insert {
  let slot=e.ids.get_or(op.target,0);let n=e.tree.nodes.at_or(slot,sequence.nil<reference.Atom>(reference.empty_atom()));
  let a=n.value;let a=reference.Atom{id:a.id,left:a.left,right:a.right,stamp:a.stamp,value:a.value,deleted:true};
  let t=sequence.set_value<reference.Atom>(e.tree,slot,a);
  return Engine{tree:sequence.set_weight<reference.Atom>(t,slot,0),ids:e.ids,deleted:e.deleted.set(op.target,true),error:0};
 }
 let atom=op.atom;let slot=e.ids.get_or(atom.id,0);
 if !reference.valid_insertion(atom) {return Engine{tree:e.tree,ids:e.ids,deleted:e.deleted,error:4};}
 if slot!=0 {
  let other=e.tree.nodes.at_or(slot,sequence.nil<reference.Atom>(reference.empty_atom())).value;
  let error:u32=choose(reference.same_insertion(atom,other),0,2);
  return Engine{tree:e.tree,ids:e.ids,deleted:e.deleted,error:error};
 }
 let left=e.ids.get_or(atom.left,0);let right=e.ids.get_or(atom.right,0);
 if (atom.left!=0 && left==0) || (mode!=2 && atom.right!=0 && right==0) ||
  (insertion_sequence && (atom.id & 4294967295)>1 && !e.ids.contains(atom.id-1)) {
  return Engine{tree:e.tree,ids:e.ids,deleted:e.deleted,error:1};
 }
 let l=located(e,left,false);let leftpos=l.rank;
 let r=right_parent(l.engine,atom,mode);let parent=r.rank;
 if mode!=2 {
  let raw=located(r.engine,right,true);
  if leftpos>=raw.rank {return Engine{tree:raw.engine.tree,ids:raw.engine.ids,deleted:raw.engine.deleted,error:4};}
  return insert_ready(raw.engine,atom,mode,left,leftpos,right,parent);
 }
 return insert_ready(r.engine,atom,mode,left,leftpos,right,parent);
}
fn insert_ready(e:Engine,atom:reference.Atom,mode:u32,left:u32,leftpos:u32,right:u32,parent:u32)->Engine {
 let current=choose(left==0,e.tree.first,e.tree.nodes.at_or(left,sequence.nil<reference.Atom>(reference.empty_atom())).next);
 let bound=e.tree.nodes.len();
 let scan=repeat_until(bound,Scan{engine:e,left:leftpos,right:right,parent:parent,current:current,destination:current,scanning:false,done:false},
  fn(s)=>s.done,fn(i)=>fn(s)=>scan_step(s,atom,mode));
 let e=scan.engine;let slot=e.tree.nodes.len();
 let atom=reference.Atom{id:atom.id,left:atom.left,right:atom.right,stamp:atom.stamp,value:atom.value,deleted:atom.deleted || e.deleted.get_or(atom.id,false)};
 return Engine{tree:sequence.insert_before<reference.Atom>(e.tree,scan.destination,atom,choose(atom.deleted,0,1)),ids:e.ids.set(atom.id,slot),deleted:e.deleted,error:0};
}
fn finish(e:Engine)->Result<List<reference.Atom>,reference.Error> {
 if e.error==1 {return Err(reference.Error.MissingDependency);}
 if e.error==2 {return Err(reference.Error.ConflictingIdentity);}
 if e.error==4 {return Err(reference.Error.InvalidOperation);}
 if e.error==5 {return Err(reference.Error.InvalidPosition);}
 if e.error!=0 {return Err(reference.Error.InvalidMode);}
 return Ok(sequence.values<reference.Atom>(e.tree,false));
}
fn replay(ops:List<reference.Operation>,mode:u32)->Result<List<reference.Atom>,reference.Error> {
 var e:Engine=empty();for op in ops {e=receive(e,op,mode);}return finish(e);
}
fn local_insert(s:Local,position:u32,value:u32,mode:u32)->Local {
 if s.engine.error!=0 {return s;}
 let root=s.engine.tree.nodes.at_or(s.engine.tree.root,sequence.nil<reference.Atom>(reference.empty_atom()));
 if position>root.live {return Local{engine:Engine{tree:s.engine.tree,ids:s.engine.ids,deleted:s.engine.deleted,error:5},counter:s.counter,stamp:s.stamp};}
 let r=sequence.seek<reference.Atom>(s.engine.tree,position,true);
 // Fugue's generator uses the previous visible atom and its immediate next
 // atom including tombstones. YATA/RGA anchor just before the next visible.
 let previous=choose(r.node==0,r.tree.last,r.tree.nodes.at_or(r.node,sequence.nil<reference.Atom>(reference.empty_atom())).previous);
 let r=choose(mode==0 || mode==3,sequence.seek<reference.Atom>(r.tree,choose(position==0,4294967295,position-1),true),r);
 let left=choose(mode==0 || mode==3,choose(position==0,0,r.node),previous);
 let right=choose(mode==0 || mode==3,choose(left==0,r.tree.first,r.tree.nodes.at_or(left,sequence.nil<reference.Atom>(reference.empty_atom())).next),r.node);
 let leftid=r.tree.nodes.at_or(left,sequence.nil<reference.Atom>(reference.empty_atom())).value.id;
 let rightid=r.tree.nodes.at_or(right,sequence.nil<reference.Atom>(reference.empty_atom())).value.id;
 let counter=s.counter+1;let stamp=s.stamp+1;
 let a=reference.Atom{id:reference.identity(1,counter),left:leftid,right:rightid,stamp:stamp,value:value,deleted:false};
 let e=Engine{tree:r.tree,ids:s.engine.ids,deleted:s.engine.deleted,error:s.engine.error};
 return Local{engine:receive(e,reference.Operation{insert:true,atom:a,target:0},mode),counter:counter,stamp:stamp};
}
fn local_delete(s:Local,position:u32,mode:u32)->Local {
 if s.engine.error!=0 {return s;}
 let root=s.engine.tree.nodes.at_or(s.engine.tree.root,sequence.nil<reference.Atom>(reference.empty_atom()));
 if position>=root.live {return Local{engine:Engine{tree:s.engine.tree,ids:s.engine.ids,deleted:s.engine.deleted,error:5},counter:s.counter,stamp:s.stamp};}
 let r=sequence.seek<reference.Atom>(s.engine.tree,position,true);
 let id=r.tree.nodes.at_or(r.node,sequence.nil<reference.Atom>(reference.empty_atom())).value.id;
 let e=Engine{tree:r.tree,ids:s.engine.ids,deleted:s.engine.deleted,error:s.engine.error};
 return Local{engine:receive(e,reference.Operation{insert:false,atom:reference.empty_atom(),target:id},mode),counter:s.counter,stamp:s.stamp+1};
}
fn local(edits:List<Edit>,mode:u32)->Result<List<reference.Atom>,reference.Error> {
 var s:Local=Local{engine:empty(),counter:0,stamp:0};
 for edit in edits {
  s=repeat_until(edit.remove,s,fn(s)=>false,fn(i)=>fn(s)=>local_delete(s,edit.position,mode));
  var position:u32=edit.position;
  for value in edit.text {s=local_insert(s,position,value,mode);position=position+1;}
 }
 return finish(s.engine);
}
