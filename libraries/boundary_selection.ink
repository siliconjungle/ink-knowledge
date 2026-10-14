module ink.knowledge.boundary_selection;
import "endpoint_index_span_graph.ink" as base;
// Full selection result is preserved; proof lives in the optional database.
fn original(engine:base.Engine,position:u32)->base.Located{
 let first=base.selected(engine,position);
 return base.selected(base.split(first.engine,first.slot,first.offset),position);
}
fn reused(engine:base.Engine,position:u32)->base.Located{
 let first=base.selected(engine,position);
 return choose(first.offset==0,first,base.selected(base.split(first.engine,first.slot,first.offset),position));
}
