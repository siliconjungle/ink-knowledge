module ink.knowledge.storage_regions;

// Relative ranges have no allocation identity. Their validity is checked against
// the supplied immutable region; callers cannot construct an arena or handle.
record Span { start:u32, count:u32, }
fn valid<T>(items:List<T>,spans:List<Span>)->Bool {
 if count(items)>4294967295 || count(spans)>4294967295 {return false;}
 let size=length(items);
 return foldr(spans,true,fn(span)=>fn(ok)=>ok && span.start<=size && span.count<=size-span.start);
}
abstract refined record Arena<T> { items:List<T>, spans:List<Span>, }
 invariant valid<T>(value.items,value.spans);
abstract refined record Handle<T> { slot:u32, extent:u32, }
 invariant value.slot<value.extent;
record Builder<T> { items:Buffer<T>, spans:Buffer<Span>, }
enum StorageError { Limit, Invalid, }

fn pack<T>(rows:List<List<T>>,maximum:u32)->Result<Arena<T>,StorageError> {
 if count(rows)>4294967295 {return Err(StorageError.Limit);}
 var builder:Builder<T>=Builder<T>{items:Buffer.empty(),spans:Buffer.empty()};
 var fits:Bool=true;
 for row in rows {
  if count(row)>4294967295 {fits=false;}
  let start=builder.items.len();let n=length(row);
  if start>maximum || n>maximum-start {fits=false;}
  if fits {
   var items:Buffer<T>=builder.items;
   for item in row {items=items.push(item);}
   builder=Builder<T>{items:items,spans:builder.spans.push(Span{start:start,count:n})};
  }
 }
 if !fits {return Err(StorageError.Limit);}
 let items=builder.items.freeze();let spans=builder.spans.freeze();
 if !valid<T>(items,spans) {return Err(StorageError.Invalid);}
 return Ok(Arena<T>{items:items,spans:spans});
}
fn size<T>(arena:Arena<T>)->u32 {return length(arena.spans);}
fn items<T>(arena:Arena<T>)->List<T> {return arena.items;}
fn spans<T>(arena:Arena<T>)->List<Span> {return arena.spans;}
fn handle<T>(arena:Arena<T>,index:u32)->Option<Handle<T>> {
 let n=length(arena.spans);
 if index<n {return Some(Handle<T>{slot:index,extent:n});}
 return None;
}
fn read<T>(arena:Arena<T>,handle:Handle<T>)->Option<List<T>> {
 if handle.extent!=length(arena.spans) {return None;}
 let span=arena.spans.at_or(handle.slot,Span{start:0,count:0});
 return Some(arena.items.drop(span.start).take(span.count));
}
fn unpack<T>(arena:Arena<T>)->List<List<T>> {
 return arena.spans.map(fn(span)=>arena.items.drop(span.start).take(span.count));
}
