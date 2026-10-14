module ink.knowledge.run_state_codec;
import "run_text_crdts.ink" as runs;
import "weighted_sequence.ink" as sequence;
import "interval_index.ink" as intervals;
record Pending{key:u64,value:Bool,}
record Stored{nodes:List<sequence.Node<u32>>,root:u32,first:u32,last:u32,fallback:u32,spans:List<runs.Span>,payload:List<u32>,intervals:List<intervals.Node>,interval_root:u32,interval_valid:Bool,pending:List<Pending>,error:u32,}
fn stored(engine:runs.Engine)->Stored{
 let keys=engine.pending.keys();var pending:Buffer<Pending>=Buffer.empty();var map:Map<u64,Bool>=engine.pending;
 for key in keys{pending=pending.push(Pending{key:key,value:map.get_or(key,false)});map=map;}
 return Stored{nodes:engine.tree.nodes.freeze(),root:engine.tree.root,first:engine.tree.first,last:engine.tree.last,fallback:engine.tree.fallback,spans:engine.spans.freeze(),payload:engine.payload.freeze(),intervals:engine.ids.nodes.freeze(),interval_root:engine.ids.root,interval_valid:engine.ids.valid,pending:pending.freeze(),error:engine.error};
}
fn loaded(s:Stored)->runs.Engine{
 var pending:Map<u64,Bool>=Map.empty();for entry in s.pending{pending=pending.set(entry.key,entry.value);}
 return runs.Engine{tree:sequence.Tree<u32>{nodes:buffer(s.nodes),root:s.root,first:s.first,last:s.last,fallback:s.fallback},spans:buffer(s.spans),payload:buffer(s.payload),ids:intervals.Index{nodes:buffer(s.intervals),root:s.interval_root,valid:s.interval_valid},pending:pending,error:s.error};
}
fn empty()->Stored{return stored(runs.empty());}
