module ink.knowledge.chunked_sequences;
enum ChunkError { Width, Limit, Invalid, }
record Builder { blocks:Buffer<List<u32>>, current:Buffer<u32>, }
fn valid(blocks:List<List<u32>>,width:u32)->Bool {
 return width>0 && count(blocks)<=4294967295
  && foldr(blocks,true,fn(block)=>fn(ok)=>ok && count(block)<=4294967295 && length(block)>0 && length(block)<=width);
}
abstract refined record Chunked { blocks:List<List<u32>>, width:u32, }
 invariant valid(value.blocks,value.width);

fn pack(words:List<u32>,width:u32)->Result<Chunked,ChunkError> {
 if width==0 {return Err(ChunkError.Width);}
 if count(words)>4294967295 {return Err(ChunkError.Limit);}
 var builder:Builder=Builder{blocks:Buffer.empty(),current:Buffer.empty()};
 for word in words {
  let current=builder.current.push(word);
  if current.len()==width {
   builder=Builder{blocks:builder.blocks.push(current.freeze()),current:Buffer.empty()};
  } else {builder=Builder{blocks:builder.blocks,current:current};}
 }
 let current=builder.current.freeze();
 let blocks=choose(length(current)==0,builder.blocks,builder.blocks.push(current)).freeze();
 if !valid(blocks,width) {return Err(ChunkError.Invalid);}
 return Ok(Chunked{blocks:blocks,width:width});
}
fn blocks(value:Chunked)->List<List<u32>> {return value.blocks;}
fn width(value:Chunked)->u32 {return value.width;}
fn unpack(value:Chunked)->List<u32> {
 return foldr(value.blocks,[],fn(block)=>fn(rest)=>block.concat(rest));
}
