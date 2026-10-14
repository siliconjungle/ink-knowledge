module ink.knowledge.causal_history_arena;
import "batched_event_graph.ink" as batches;
record Row{id:u64,position:u32,remove:u32,parent_start:u32,parent_end:u32,text_start:u32,text_end:u32,}
record Stored{rows:List<Row>,parents:List<u64>,text:List<u32>,}
record Arena{rows:Buffer<Row>,parents:Buffer<u64>,text:Buffer<u32>,}
fn nil()->Row{return Row{id:0,position:0,remove:0,parent_start:0,parent_end:0,text_start:0,text_end:0};}
fn empty()->Stored{return Stored{rows:[],parents:[],text:[]};}
fn loaded(s:Stored)->Arena{return Arena{rows:buffer(s.rows),parents:buffer(s.parents),text:buffer(s.text)};}
fn stored(a:Arena)->Stored{return Stored{rows:a.rows.freeze(),parents:a.parents.freeze(),text:a.text.freeze()};}
record Equal{arena:Arena,equal:Bool,}
record Checking{arena:Arena,equal:Bool,}
fn check_parent(x:Checking,index:u32,value:u64)->Checking{let same=x.equal && x.arena.parents.at_or(index,0)==value;return Checking{arena:x.arena,equal:same};}
fn check_text(x:Checking,index:u32,value:u32)->Checking{let same=x.equal && x.arena.text.at_or(index,0)==value;return Checking{arena:x.arena,equal:same};}
fn equal(a:Arena,slot:u32,c:batches.Change)->Equal{
 let row=a.rows.at_or(slot,nil());
 let metadata=slot<a.rows.len() && row.id==c.id && row.position==c.position && row.remove==c.remove && row.parent_start<=row.parent_end && row.parent_end<=a.parents.len() && row.text_start<=row.text_end && row.text_end<=a.text.len() && row.parent_end-row.parent_start==length(c.parents) && row.text_end-row.text_start==length(c.text);
 let ps=row.parent_start;let ts=row.text_start;let parents=c.parents;let text=c.text;
 let checked=repeat_until(length(parents),Checking{arena:a,equal:metadata},fn(x)=>!x.equal,fn(i,x)=>check_parent(x,ps+i,parents.at_or(i,0)));
 let checked=repeat_until(length(text),checked,fn(x)=>!x.equal,fn(i,x)=>check_text(x,ts+i,text.at_or(i,0)));
 return Equal{arena:checked.arena,equal:checked.equal};
}
record Reading{arena:Arena,values:Buffer<batches.Change>,index:u32,}
record Parents{arena:Arena,values:Buffer<u64>,}
record Text{arena:Arena,values:Buffer<u32>,}
fn read_parent(p:Parents,index:u32)->Parents{let value=p.arena.parents.at_or(index,0);return Parents{arena:p.arena,values:p.values.push(value)};}
fn read_text(t:Text,index:u32)->Text{let value=t.arena.text.at_or(index,0);return Text{arena:t.arena,values:t.values.push(value)};}
fn read_step(r:Reading)->Reading{
 let row=r.arena.rows.at_or(r.index,nil());let ps=row.parent_start;let ts=row.text_start;
 let p=repeat_until(row.parent_end-ps,Parents{arena:r.arena,values:Buffer.empty()},fn(p)=>false,fn(i,p)=>read_parent(p,ps+i));
 let t=repeat_until(row.text_end-ts,Text{arena:p.arena,values:Buffer.empty()},fn(t)=>false,fn(i,t)=>read_text(t,ts+i));
 return Reading{arena:t.arena,values:r.values.push(batches.Change{id:row.id,parents:p.values.freeze(),position:row.position,remove:row.remove,text:t.values.freeze()}),index:r.index+1};
}
fn decoded(s:Stored)->List<batches.Change>{let count=length(s.rows);let r=repeat_until(count,Reading{arena:loaded(s),values:Buffer.empty(),index:0},fn(r)=>false,fn(i,r)=>read_step(r));return r.values.freeze();}
fn appended(a:Arena,c:batches.Change)->Arena{
 let ps=a.parents.len();let ts=a.text.len();let pe=ps+length(c.parents);let te=ts+length(c.text);
 return Arena{rows:a.rows.push(Row{id:c.id,position:c.position,remove:c.remove,parent_start:ps,parent_end:pe,text_start:ts,text_end:te}),parents:a.parents.append(buffer(c.parents)),text:a.text.append(buffer(c.text))};
}
