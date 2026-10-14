module ink.knowledge.incremental_blocked_interval_index;
// General disjoint half-open u64 intervals. End zero denotes 2^64.
// Stable entry handles survive B+ tree splits; leaves have linked neighbors.
// Child insertion reindexes only its shifted suffix. Minimum propagation stops
// when its stored value is unchanged. Both rely on maintained block metadata.
// Ordinary source algorithm, with no database rewrite authority yet.
record Node{start:u64,end:u64,value:u32,leaf:u32,index:u32,previous:u32,next:u32,}
record Block{start:u32,count:u32,parent:u32,index:u32,leaf:Bool,minimum:u64,}
record Index{nodes:Buffer<Node>,blocks:Buffer<Block>,children:Buffer<u32>,root:u32,valid:Bool,}
record Found{index:Index,value:u32,start:u64,end:u64,hint:u32,}
fn nil()->Node{return Node{start:0,end:0,value:0,leaf:0,index:0,previous:0,next:0};}
fn empty_block()->Block{return Block{start:0,count:0,parent:0,index:0,leaf:true,minimum:0};}
fn empty()->Index{return Index{nodes:buffer([nil()]),blocks:buffer([empty_block(),Block{..empty_block(),start:33}]),children:buffer_fill(66,0),root:1,valid:true};}
record Bound{index:Index,block:u32,low:u32,high:u32,key:u64,}
fn bound_step(s:Bound)->Bound{
 let b=s.index.blocks.at_or(s.block,empty_block());let mid=s.low+quot_or(s.high-s.low,2,0);
 let slot=s.index.children.at_or(b.start+mid,0);
 let key=choose(b.leaf,s.index.nodes.at_or(slot,nil()).start,s.index.blocks.at_or(slot,empty_block()).minimum);
 return choose(key<=s.key,Bound{..s,low:mid+1},Bound{..s,high:mid});
}
record Search{index:Index,block:u32,position:u32,done:Bool,}
fn search_step(s:Search,key:u64)->Search{
 let b=s.index.blocks.at_or(s.block,empty_block());
 let r=repeat_until(6,Bound{index:s.index,block:s.block,low:0,high:b.count,key:key},fn(r)=>r.low>=r.high,fn(i,r)=>bound_step(r));
 if b.leaf{return Search{index:r.index,block:s.block,position:r.low,done:true};}
 let child=r.index.children.at_or(b.start+choose(r.low==0,0,r.low-1),0);
 return Search{index:r.index,block:child,position:0,done:child==0};
}
fn search(index:Index,key:u64)->Search{
 let root=index.root;let bound=index.blocks.len();
 return repeat_until(bound,Search{index:index,block:root,position:0,done:false},fn(s)=>s.done,fn(i,s)=>search_step(s,key));
}
fn locate(index:Index,key:u64)->Found{return hinted(index,key,0);}
fn hinted(index:Index,key:u64,hint:u32)->Found{
 let n=index.nodes.at_or(hint,nil());
 if index.valid && hint!=0 && hint<index.nodes.len() && n.value!=0 && n.start<=key && (n.end==0 || key<n.end){return Found{index:index,value:n.value,start:n.start,end:n.end,hint:hint};}
 let s=search(index,key);let b=s.index.blocks.at_or(s.block,empty_block());
 let first=s.index.children.at_or(b.start,0);let prior=s.index.nodes.at_or(first,nil()).previous;
 let slot=choose(s.position==0,prior,s.index.children.at_or(b.start+s.position-1,0));let n=s.index.nodes.at_or(slot,nil());
 let value=choose(slot!=0 && n.start<=key && (n.end==0 || key<n.end),n.value,0);
 return Found{index:s.index,value:value,start:n.start,end:n.end,hint:choose(value==0,0,slot)};
}
record Indexed{index:Index,block:u32,position:u32,}
fn index_step(s:Indexed)->Indexed{
 let b=s.index.blocks.at_or(s.block,empty_block());let slot=s.index.children.at_or(b.start+s.position,0);let t=s.index;
 if b.leaf{let n=t.nodes.at_or(slot,nil());return Indexed{index:Index{..t,nodes:t.nodes.set(slot,Node{..n,leaf:s.block,index:s.position})},block:s.block,position:s.position+1};}
 let n=t.blocks.at_or(slot,empty_block());return Indexed{index:Index{..t,blocks:t.blocks.set(slot,Block{..n,parent:s.block,index:s.position})},block:s.block,position:s.position+1};
}
fn indexed(t:Index,block:u32)->Index{
 let count=t.blocks.at_or(block,empty_block()).count;let r=repeat_until(count,Indexed{index:t,block:block,position:0},fn(r)=>false,fn(i,r)=>index_step(r));return r.index;
}
record Minimum{index:Index,block:u32,}
fn minimum_step(s:Minimum)->Minimum{
 let b=s.index.blocks.at_or(s.block,empty_block());let slot=s.index.children.at_or(b.start,0);
 let value=choose(b.leaf,s.index.nodes.at_or(slot,nil()).start,s.index.blocks.at_or(slot,empty_block()).minimum);let t=s.index;
 return Minimum{index:Index{..t,blocks:t.blocks.set(s.block,Block{..b,minimum:value})},block:choose(b.minimum==value,0,b.parent)};
}
fn minima(t:Index,block:u32)->Index{let count=t.blocks.len();let r=repeat_until(count,Minimum{index:t,block:block},fn(r)=>r.block==0,fn(i,r)=>minimum_step(r));return r.index;}
fn added(t:Index,block:u32,position:u32,slot:u32)->Index{
 let b=t.blocks.at_or(block,empty_block());let children=t.children.copy_within(b.start+position,b.start+position+1,b.count-position).set(b.start+position,slot);
 let t=Index{..t,blocks:t.blocks.set(block,Block{..b,count:b.count+1}),children:children};
 let count=b.count+1-position;let r=repeat_until(count,Indexed{index:t,block:block,position:position},fn(r)=>false,fn(i,r)=>index_step(r));return r.index;
}
record Splitting{index:Index,block:u32,}
fn split_step(s:Splitting)->Splitting{
 let b=s.index.blocks.at_or(s.block,empty_block());if b.count<=32{return Splitting{index:s.index,block:0};}
 let t=s.index;let right=t.blocks.len();let start=t.children.len();
 let children=t.children.append(buffer_fill(33,0)).copy_within(b.start+16,start,b.count-16);
 let blocks=t.blocks.set(s.block,Block{..b,count:16}).push(Block{..b,start:start,count:b.count-16,index:b.index+1});
 let t=indexed(indexed(Index{..t,blocks:blocks,children:children},s.block),right);
 let t=minima(minima(t,s.block),right);
 if b.parent!=0{return Splitting{index:added(t,b.parent,b.index+1,right),block:b.parent};}
 let root=t.blocks.len();let start=t.children.len();let children=t.children.append(buffer_fill(33,0)).set(start,s.block).set(start+1,right);
 let t=Index{..t,blocks:t.blocks.push(Block{start:start,count:2,parent:0,index:0,leaf:false,minimum:b.minimum}),children:children,root:root};
 return Splitting{index:minima(indexed(t,root),root),block:0};
}
fn insert(index:Index,start:u64,end:u64,value:u32)->Index{
 let s=search(index,start);let b=s.index.blocks.at_or(s.block,empty_block());let first=s.index.children.at_or(b.start,0);
 let prior=choose(s.position==0,s.index.nodes.at_or(first,nil()).previous,s.index.children.at_or(b.start+s.position-1,0));
 let before=s.index.nodes.at_or(prior,nil());let next=choose(prior==0,first,before.next);let after=s.index.nodes.at_or(next,nil());
 let valid=s.index.valid && (start<end || end==0) && value!=0 && (prior==0 || (before.end!=0 && start>=before.end)) && (next==0 || (end!=0 && end<=after.start));
 if !valid{return Index{..s.index,valid:false};}
 let t=s.index;let slot=t.nodes.len();let nodes=t.nodes.push(Node{start:start,end:end,value:value,leaf:s.block,index:s.position,previous:prior,next:next});
 let nodes=choose(prior==0,nodes,nodes.set(prior,Node{..before,next:slot}));let nodes=choose(next==0,nodes,nodes.set(next,Node{..after,previous:slot}));
 let t=minima(added(Index{..t,nodes:nodes},s.block,s.position,slot),s.block);let bound=t.blocks.len()+1;
 return repeat_until(bound,Splitting{index:t,block:s.block},fn(s)=>s.block==0,fn(i,s)=>split_step(s)).index;
}
fn changed_end(index:Index,start:u64,end:u64)->Index{
 let f=locate(index,start);let n=f.index.nodes.at_or(f.hint,nil());let next=f.index.nodes.at_or(n.next,nil());
 let valid=f.index.valid && f.hint!=0 && n.start==start && (start<end || end==0) && (n.next==0 || (end!=0 && end<=next.start));
 let index=f.index;let nodes=choose(valid,index.nodes.set(f.hint,Node{..n,end:end}),index.nodes);return Index{..index,nodes:nodes,valid:valid};
}
fn partition(index:Index,start:u64,end:u64,cut:u64,value:u32,suffix:u32,hint:u32)->Index{
 let n=index.nodes.at_or(hint,nil());
 let valid=index.valid && hint!=0 && hint<index.nodes.len() && n.start==start && n.end==end && n.value==value && value!=0 && suffix!=0 && start<cut && (end==0 || cut<end);
 if !valid{return insert(changed_end(index,start,cut),cut,end,suffix);}
 let nodes=index.nodes.set(hint,Node{..n,end:cut});let t=Index{..index,nodes:nodes};let slot=t.nodes.len();let after=t.nodes.at_or(n.next,nil());
 let nodes=t.nodes.push(Node{start:cut,end:end,value:suffix,leaf:n.leaf,index:n.index+1,previous:hint,next:n.next});
 let nodes=nodes.set(hint,Node{..n,end:cut,next:slot});let nodes=choose(n.next==0,nodes,nodes.set(n.next,Node{..after,previous:slot}));
 let t=added(Index{..t,nodes:nodes},n.leaf,n.index+1,slot);let bound=t.blocks.len()+1;
 return repeat_until(bound,Splitting{index:t,block:n.leaf},fn(s)=>s.block==0,fn(i,s)=>split_step(s)).index;
}
