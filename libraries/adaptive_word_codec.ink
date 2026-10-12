module ink.knowledge.adaptive_word_codec;
import "codecs.ink" as rle;
// Tagged word format. Tag 0 carries raw words, tag 1 carries the RLE format.
// Compressed output is chosen only when it is no larger; neither tag denotes LZ4.
fn encode(xs:List<u32>)->List<u32>{
 let n=length(xs);var previous:u32=0;var started:Bool=false;var runs:u32=0;
 for word in xs {if !started || word!=previous {runs=runs+1;}started=true;previous=word;}
 if runs>quot_or(n,2,0) {let prefix:List<u32>=[0,n];return prefix.concat(xs);}
 let prefix:List<u32>=[1];return prefix.concat(rle.encode_runs(xs));
}
fn decode(words:List<u32>,maximum:u32)->Result<List<u32>,rle.DecodeError>{
 if length(words)<2 {return Err(rle.DecodeError.Invalid);}
 let size=words.at_or(1,0);
 if size>maximum {return Err(rle.DecodeError.Limit);}
 let tag=words.at_or(0,2);
 if tag==0 {if size!=length(words)-2 {return Err(rle.DecodeError.Invalid);}return Ok(words.drop(2));}
 if tag==1 {return rle.decode_runs(words.drop(1),maximum);}
 return Err(rle.DecodeError.Invalid);
}
