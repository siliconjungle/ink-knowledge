module ink.knowledge.chunked_sequences;
enum ChunkError { Width, Limit, Invalid, }
record Builder<T> { blocks:Buffer<List<T>>, current:Buffer<T>, }
fn valid<T>(blocks:List<List<T>>,width:u32)->Bool {
 return width>0 && count(blocks)<=4294967295
  && foldr(blocks,true,fn(block)=>fn(ok)=>ok && count(block)<=4294967295 && length(block)>0 && length(block)<=width);
}
abstract refined record Chunked<T> { blocks:List<List<T>>, width:u32, }
 invariant valid<T>(value.blocks,value.width);

fn pack<T>(items:List<T>,width:u32)->Result<Chunked<T>,ChunkError> {
 if width==0 {return Err(ChunkError.Width);}
 if count(items)>4294967295 {return Err(ChunkError.Limit);}
 var builder:Builder<T>=Builder<T>{blocks:Buffer.empty(),current:Buffer.empty()};
 for item in items {
  let current=builder.current.push(item);
  if current.len()==width {
   builder=Builder<T>{blocks:builder.blocks.push(current.freeze()),current:Buffer.empty()};
  } else {builder=Builder<T>{blocks:builder.blocks,current:current};}
 }
 let current=builder.current.freeze();
 let blocks=choose(length(current)==0,builder.blocks,builder.blocks.push(current)).freeze();
 if !valid<T>(blocks,width) {return Err(ChunkError.Invalid);}
 return Ok(Chunked<T>{blocks:blocks,width:width});
}
fn blocks<T>(value:Chunked<T>)->List<List<T>> {return value.blocks;}
fn width<T>(value:Chunked<T>)->u32 {return value.width;}
fn unpack<T>(value:Chunked<T>)->List<T> {
 return foldr(value.blocks,[],fn(block)=>fn(rest)=>block.concat(rest));
}
