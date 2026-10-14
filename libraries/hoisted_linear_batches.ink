module ink.knowledge.hoisted_linear_batches;
import "batched_event_graph.ink" as batches;
import "gap_sequence.ink" as gap;
import "text_crdts.ink" as reference;
// Speculative ordinary source. Parent-chain validation shares the edit pass;
// failure leaves the caller free to use its complete existing implementation.
record Checked{linear:batches.Linear,previous:u64,}
fn step(s:Checked,c:batches.Change)->Checked{
 let follows=choose(s.previous==0,length(c.parents)==0,length(c.parents)==1 && c.parents.at_or(0,0)==s.previous);
 if !follows{let l=s.linear;return Checked{linear:batches.Linear{..l,error:4},previous:s.previous};}
 let previous=c.id+batches.width(c)-1;
 return Checked{linear:batches.linear_step(s.linear,c),previous:previous};
}
fn attempted(changes:List<batches.Change>)->Result<List<u32>,reference.Error>{
 let initial=Checked{linear:batches.Linear{data:gap.empty<u32>(0),actors:Map.empty(),error:0},previous:0};
 let s=fold_until(changes,initial,fn(c,s)=>s.linear.error!=0,fn(c,s)=>step(s,c));
 return choose(s.linear.error==0,Ok(gap.freeze<u32>(s.linear.data)),Err(reference.Error.InvalidOperation));
}
