module ink.knowledge.ecs;
import "buffers.ink" as ranges;
record Column<T>{entities:List<u32>,values:List<T>,}
enum ColumnError { Length, Duplicate, }
// Stable physical row order is explicit. Entity IDs remain logical values.
fn remove_range<T>(column:Column<T>,start:u32,count:u32)->Result<Column<T>,ColumnError>{
 if length(column.entities)!=length(column.values) {return Err(ColumnError.Length);}
 return Ok(Column<T>{entities:ranges.erase_range<u32>(column.entities,start,count),values:ranges.erase_range<T>(column.values,start,count)});
}
// A sparse component lookup in requested entity order. Build once per batch,
// retain missing values as None, and reject ambiguous duplicate component IDs.
fn gather<T>(column:Column<T>,entities:List<u32>,fallback:T)->Result<List<Option<T>>,ColumnError>{
 if length(column.entities)!=length(column.values) {return Err(ColumnError.Length);}
 var index:Map<u32,T>=Map.empty();var at:u32=0;var valid:Bool=true;
 for entity in column.entities {
  if index.contains(entity) {valid=false;}
  index=index.set(entity,column.values.at_or(at,fallback));at=at+1;
 }
 if !valid {return Err(ColumnError.Duplicate);}
 var output:Buffer<Option<T>>=Buffer.empty();
 for entity in entities {
  if index.contains(entity) {output=output.push(Some(index.get_or(entity,fallback)));}
  else {output=output.push(None);}
 }
 return Ok(output.freeze());
}
