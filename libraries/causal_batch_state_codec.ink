module ink.knowledge.causal_batch_state_codec;
import "whole_target_span_graph.ink" as spans;
import "blocked_measure_sequence.ink" as sequence;
import "interval_index.ink" as intervals;
import "view_pair_causal_workspace.ink" as causal;
import "ragged_buffer.ink" as ragged;
record End{key:u64,value:u32,}
record Stored{
 identity_hint:u32,insert_hint:u32,nodes:List<sequence.Node<u32>>,blocks:List<sequence.Block>,children:List<u32>,root:u32,first:u32,last:u32,fallback:u32,
 spans:List<spans.Span>,payload:List<u32>,ids:List<intervals.Node>,ids_root:u32,ids_valid:Bool,engine_error:u32,
 graph:List<causal.Node>,frontiers:List<List<u32>>,marks:List<causal.Mark>,queue:List<u32>,removed:List<causal.Range>,added:List<causal.Range>,generation:u32,graph_valid:Bool,
 ends:List<End>,identities:List<intervals.Node>,identities_root:u32,identities_valid:Bool,targets:List<spans.Target>,ranges:List<ragged.Range>,last_id:u64,error:u32,
}
fn stored(w:spans.Walker)->Stored{
 let keys=w.ends.keys();var ends:Buffer<End>=Buffer.empty();var map:Map<u64,u32>=w.ends;
 for key in keys{ends=ends.push(End{key:key,value:map.get_or(key,0)});map=map;}
 return Stored{identity_hint:w.identity_hint,insert_hint:w.engine.insert_hint,nodes:w.engine.tree.nodes.freeze(),blocks:w.engine.tree.blocks.freeze(),children:w.engine.tree.children.freeze(),root:w.engine.tree.root,first:w.engine.tree.first,last:w.engine.tree.last,fallback:w.engine.tree.fallback,
 spans:w.engine.spans.freeze(),payload:w.engine.payload.freeze(),ids:w.engine.ids.nodes.freeze(),ids_root:w.engine.ids.root,ids_valid:w.engine.ids.valid,engine_error:w.engine.error,
 graph:w.graph.nodes.freeze(),frontiers:w.graph.frontiers.freeze(),marks:w.graph.marks.freeze(),queue:w.graph.queue.freeze(),removed:w.graph.removed.freeze(),added:w.graph.added.freeze(),generation:w.graph.generation,graph_valid:w.graph.valid,
 ends:ends.freeze(),identities:w.identities.nodes.freeze(),identities_root:w.identities.root,identities_valid:w.identities.valid,targets:w.applied.values.freeze(),ranges:w.applied.ranges.freeze(),last_id:w.last,error:w.error};
}
fn loaded(s:Stored)->spans.Walker{
 var ends:Map<u64,u32>=Map.empty();for entry in s.ends{ends=ends.set(entry.key,entry.value);}
 return spans.Walker{identity_hint:s.identity_hint,
 engine:spans.Engine{insert_hint:s.insert_hint,tree:sequence.Tree<u32>{nodes:buffer(s.nodes),blocks:buffer(s.blocks),children:buffer(s.children),root:s.root,first:s.first,last:s.last,fallback:s.fallback},spans:buffer(s.spans),payload:buffer(s.payload),ids:intervals.Index{nodes:buffer(s.ids),root:s.ids_root,valid:s.ids_valid},error:s.engine_error},
 graph:causal.Graph{nodes:buffer(s.graph),frontiers:buffer(s.frontiers),marks:buffer(s.marks),queue:buffer(s.queue),removed:buffer(s.removed),added:buffer(s.added),generation:s.generation,valid:s.graph_valid},
 ends:ends,identities:intervals.Index{nodes:buffer(s.identities),root:s.identities_root,valid:s.identities_valid},applied:ragged.Rows<spans.Target>{values:buffer(s.targets),ranges:buffer(s.ranges)},last:s.last_id,error:s.error};
}
fn empty()->Stored{return stored(spans.empty());}
