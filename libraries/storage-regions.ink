module ink.knowledge.storage_regions;

// Relative ranges have no allocation identity. Their validity is checked against
// the supplied immutable region; callers cannot construct an arena or handle.
record Span { start:u32, count:u32, }
fn valid(words:List<u32>,spans:List<Span>)->Bool {
 if count(words)>4294967295 || count(spans)>4294967295 {return false;}
 let size=length(words);
 return foldr(spans,true,fn(span)=>fn(ok)=>ok && span.start<=size && span.count<=size-span.start);
}
abstract refined record Arena { words:List<u32>, spans:List<Span>, }
 invariant valid(value.words,value.spans);
abstract refined record Handle { slot:u32, extent:u32, }
 invariant value.slot<value.extent;
record Builder { words:Buffer<u32>, spans:Buffer<Span>, }
enum StorageError { Limit, Invalid, }

fn pack(rows:List<List<u32>>,maximum:u32)->Result<Arena,StorageError> {
 if count(rows)>4294967295 {return Err(StorageError.Limit);}
 var builder:Builder=Builder{words:Buffer.empty(),spans:Buffer.empty()};
 var fits:Bool=true;
 for row in rows {
  if count(row)>4294967295 {fits=false;}
  let start=builder.words.len();let n=length(row);
  if start>maximum || n>maximum-start {fits=false;}
  if fits {
   var words:Buffer<u32>=builder.words;
   for word in row {words=words.push(word);}
   builder=Builder{words:words,spans:builder.spans.push(Span{start:start,count:n})};
  }
 }
 if !fits {return Err(StorageError.Limit);}
 let words=builder.words.freeze();let spans=builder.spans.freeze();
 if !valid(words,spans) {return Err(StorageError.Invalid);}
 return Ok(Arena{words:words,spans:spans});
}
fn size(arena:Arena)->u32 {return length(arena.spans);}
fn words(arena:Arena)->List<u32> {return arena.words;}
fn spans(arena:Arena)->List<Span> {return arena.spans;}
fn handle(arena:Arena,index:u32)->Option<Handle> {
 let n=length(arena.spans);
 if index<n {return Some(Handle{slot:index,extent:n});}
 return None;
}
fn read(arena:Arena,handle:Handle)->Option<List<u32>> {
 if handle.extent!=length(arena.spans) {return None;}
 let span=arena.spans.at_or(handle.slot,Span{start:0,count:0});
 return Some(arena.words.drop(span.start).take(span.count));
}
fn unpack(arena:Arena)->List<List<u32>> {
 return arena.spans.map(fn(span)=>arena.words.drop(span.start).take(span.count));
}
