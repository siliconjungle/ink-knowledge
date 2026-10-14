module ink.knowledge.flat_pair_causal_workspace;
import "priority_queue.ink" as heap;
import "ragged_buffer.ink" as ragged;

// Append-only DAG and invocation-local query workspace. Most nodes keep their
// first two parents as scalars; only larger frontiers occupy a list slot.
// Epoch-tagged flags and retained heap/output buffers avoid allocating a map
// and new vectors for each difference query. These are ordinary algorithms,
// not compiler capabilities or an admitted rewrite of causal_ranges.
record Node{base:u32,parent:u32,second:u32,frontier:u32,}
record Mark{epoch:u32,flag:u32,}
record Range{start:u32,end:u32,}
record Graph{nodes:Buffer<Node>,frontiers:ragged.Rows<u32>,marks:Buffer<Mark>,
 queue:Buffer<u32>,removed:Buffer<Range>,added:Buffer<Range>,generation:u32,valid:Bool,}
record Work{graph:Graph,flags:Buffer<Mark>,queue:Buffer<u32>,generation:u32,shared:u32,
 removed:Buffer<Range>,added:Buffer<Range>,valid:Bool,}
record Difference{graph:Graph,removed:Buffer<Range>,added:Buffer<Range>,valid:Bool,}
record Run{work:Work,version:u32,flag:u32,base:u32,}
fn nil()->Node{return Node{base:0,parent:0,second:0,frontier:0};}
fn unmarked()->Mark{return Mark{epoch:0,flag:0};}
fn empty()->Graph{return Graph{nodes:buffer([nil()]),frontiers:ragged.Rows<u32>{values:Buffer.empty(),ranges:buffer([ragged.nil()])},marks:buffer([unmarked()]),
 queue:Buffer.empty(),removed:Buffer.empty(),added:Buffer.empty(),generation:0,valid:true};}
fn append(g:Graph,parents:List<u32>)->Graph{
 let slot=g.nodes.len();let previous=g.nodes.at_or(slot-1,nil());let count=length(parents);let parent=parents.at_or(0,0);
 let base=choose(count==1 && parent==slot-1,previous.base,slot);
 let valid=g.valid && foldl(parents,true,fn(p,ok)=>ok && p>0 && p<slot);
 let frontier=choose(count>2,g.frontiers.ranges.len(),0);
 let frontiers=choose(count>2,ragged.append<u32>(g.frontiers,buffer(parents)),g.frontiers);
 let node=Node{base:base,parent:choose(count<=2,parent,0),second:choose(count==2,parents.at_or(1,0),0),frontier:frontier};
 return Graph{..g,nodes:g.nodes.push(node),frontiers:frontiers,marks:g.marks.push(unmarked()),valid:valid};
}
// Read-only flag lookup must return its affine workspace unchanged.
record Flagged{work:Work,value:u32,}
fn observed(w:Work,version:u32)->Flagged{
 let m=w.flags.at_or(version,unmarked());let value=choose(m.epoch==w.generation,m.flag,0);
 return Flagged{work:w,value:value};
}
fn enq(w:Work,version:u32,added:u32)->Work{
 if version==0 || version>=w.graph.nodes.len(){return Work{..w,valid:false};}
 let f=observed(w,version);let current=f.value;let w=f.work;
 if current==0{
  return Work{..w,queue:heap.push(w.queue,version),flags:w.flags.set(version,Mark{epoch:w.generation,flag:added}),shared:w.shared+choose(added==3,1,0)};
 }
 let changed=current!=added && current!=3;
 return Work{..w,flags:w.flags.set(version,Mark{epoch:w.generation,flag:choose(changed,3,current)}),shared:w.shared+choose(changed,1,0)};
}
fn mark(w:Work,start:u32,end:u32,flag:u32)->Work{
 if start>=end || flag==3{return w;}
 let range=Range{start:start,end:end};
 return Work{..w,removed:choose(flag==1,w.removed.push(range),w.removed),added:choose(flag==2,w.added.push(range),w.added)};
}
fn consume(r:Run)->Run{
 let version=r.work.queue.at_or(0,0);let f=observed(r.work,version);let flag=f.value;
 let w=f.work;let shared=w.shared-choose(flag==3,1,0);let w=Work{..w,queue:heap.pop(w.queue),shared:shared};
 let w=choose(flag!=r.flag,mark(w,version+1,r.version+1,r.flag),w);
 return Run{work:w,version:choose(flag!=r.flag,version,r.version),flag:choose(flag!=r.flag,3,r.flag),base:r.base};
}
record Parents{work:Work,index:u32,end:u32,flag:u32,}
fn parent_step(p:Parents)->Parents{
 let parent=p.work.graph.frontiers.values.at_or(p.index,0);let index=p.index+1;let end=p.end;let flag=p.flag;
 return Parents{work:enq(p.work,parent,flag),index:index,end:end,flag:flag};
}
fn step(w:Work)->Work{
 let version=w.queue.at_or(0,0);let f=observed(w,version);let flag=f.value;let w=f.work;
 let node=w.graph.nodes.at_or(version,nil());let base=node.base;let bound=w.queue.len();
 let w=Work{..w,queue:heap.pop(w.queue),shared:w.shared-choose(flag==3,1,0)};
 let r=repeat_until(bound,Run{work:w,version:version,flag:flag,base:base},fn(r)=>r.work.queue.len()==0 || r.work.queue.at_or(0,0)<r.base,fn(i,r)=>consume(r));
 let node=r.work.graph.nodes.at_or(base,nil());let flag=r.flag;
 let w=mark(r.work,base,r.version+1,flag);
 if node.frontier==0{
  let w=choose(node.parent==0,w,enq(w,node.parent,flag));
  return choose(node.second==0,w,enq(w,node.second,flag));
 }
 let range=w.graph.frontiers.ranges.at_or(node.frontier,ragged.nil());let bound=range.end-range.start;
 let p=repeat_until(bound,Parents{work:w,index:range.start,end:range.end,flag:flag},fn(p)=>p.index>=p.end,fn(i,p)=>parent_step(p));
 return p.work;
}
fn difference(g:Graph,left:List<u32>,right:List<u32>)->Difference{
 let bound=g.nodes.len();let valid=g.valid && g.marks.len()==bound;
 let rollover=g.generation==4294967295;let generation=choose(rollover,1,g.generation+1);
 let flags=choose(rollover,g.marks.fill_range(0,bound,unmarked()),g.marks);
 let queue=g.queue.truncate(0);let removed=g.removed.truncate(0);let added=g.added.truncate(0);
 let g=Graph{..g,marks:Buffer.empty(),queue:Buffer.empty(),removed:Buffer.empty(),added:Buffer.empty(),generation:generation};
 var w:Work=Work{graph:g,flags:flags,queue:queue,generation:generation,shared:0,removed:removed,added:added,valid:valid};
 for p in left{w=enq(w,p,1);}for p in right{w=enq(w,p,2);}
 let w=repeat_until(bound,w,fn(w)=>!w.valid || w.queue.len()<=w.shared,fn(i,w)=>step(w));
 let g=w.graph;let g=Graph{..g,marks:w.flags,queue:w.queue};
 return Difference{graph:g,removed:w.removed,added:w.added,valid:w.valid};
}
fn recycled(g:Graph,removed:Buffer<Range>,added:Buffer<Range>)->Graph{
 return Graph{..g,removed:removed,added:added};
}
