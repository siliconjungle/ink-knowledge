module ink.knowledge.codecs;
enum DecodeError { Invalid, Limit, }
// Portable word-stream format: decoded length, then (positive count,value)
// pairs. This is a u32 word codec, not an implicit packed-byte transport.
fn encode_runs(xs:List<u32>)->List<u32>{
 var output:Buffer<u32>=buffer([length(xs)]);
 var started:Bool=false;var previous:u32=0;var count:u32=0;
 for value in xs {
  if started && value!=previous {output=output.push(count).push(previous);count=0;}
  started=true;previous=value;count=count+1;
 }
 if started {output=output.push(count).push(previous);}
 return output.freeze();
}
fn decode_runs(words:List<u32>,maximum:u32)->Result<List<u32>,DecodeError>{
 let size=length(words);
 if size==0 || rem_or(size-1,2,0)!=0 {return Err(DecodeError.Invalid);}
 let length=words.at_or(0,0);
 if length>maximum {return Err(DecodeError.Limit);}
 var output:Buffer<u32>=buffer_fill(length,0);
 var position:u32=0;var count:u32=0;var want_count:Bool=true;var valid:Bool=true;
 for word in words.drop(1) {
  if want_count {count=word;want_count=false;}
  else {
   if count==0 || count>length-position {valid=false;}
   if valid {output=output.fill_range(position,count,word);position=position+count;}
   want_count=true;
  }
 }
 if !valid || position!=length {return Err(DecodeError.Invalid);}
 return Ok(output.freeze());
}

// Canonical byte-value serialisation into packed little-endian u32 words.
// The first word records the number of octets. Final unused lanes must be zero.
fn pack_octets(bytes:List<u32>)->Result<List<u32>,DecodeError>{
 var output:Buffer<u32>=buffer([length(bytes)]);
 var packed:u32=0;var lanes:u32=0;var valid:Bool=true;
 for byte in bytes {
  if byte>255 {valid=false;}
  packed=packed | wrapping_shl(byte,lanes*8);lanes=lanes+1;
  if lanes==4 {output=output.push(packed);packed=0;lanes=0;}
 }
 if !valid {return Err(DecodeError.Invalid);}
 if lanes>0 {output=output.push(packed);}
 return Ok(output.freeze());
}
fn unpack_octets(words:List<u32>,maximum:u32)->Result<List<u32>,DecodeError>{
 if length(words)==0 {return Err(DecodeError.Invalid);}
 let size=words.at_or(0,0);
 if size>maximum {return Err(DecodeError.Limit);}
 let expected=1+quot_or(size,4,0)+choose(rem_or(size,4,0)>0,1,0);
 if length(words)!=expected {return Err(DecodeError.Invalid);}
 var output:Buffer<u32>=buffer_fill(size,0);var at:u32=0;var valid:Bool=true;
 for word in words.drop(1) {
  var pending:u32=word;
  for lane in 0..4 {
   if at<size {output=output.set(at,pending & 255);at=at+1;}
   else {if pending!=0 {valid=false;}}
   pending=wrapping_shr(pending,8);
  }
 }
 if !valid {return Err(DecodeError.Invalid);}
 return Ok(output.freeze());
}
