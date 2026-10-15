module ink.knowledge.bit_automata;

// Independently authored bit-state algorithms, motivated by Handwired's packed
// circuit execution. These are ordinary source definitions, not compiler cases.
record Cursor { active:u32, matches:u32, }
record Literal { masks:List<u32>, accept:u32, width:u32, }

// Shift-And: bit j records whether a prefix ending at position j is active.
fn transition(active:u32,mask:u32)->u32 {
 return (wrapping_shl(active,1) | 1) & mask;
}
fn step(cursor:Cursor,mask:u32,accept:u32)->Cursor {
 let active=transition(cursor.active,mask);
 let matched=(active & accept)!=0;
 return Cursor{active:choose(matched,0,active),matches:cursor.matches+choose(matched,1,0)};
}

// This checked constructor admits nonempty octet literals of at most 32 lanes.
// Input zero is allowed here: an application that uses padding must separately
// ensure that its pattern does not match padding, or pass the actual length.
fn literal(symbols:List<u32>)->Option<Literal> {
 let width=length(symbols);
 if width==0 || width>32 {return None;}
 var masks:Buffer<u32>=buffer_fill(256,0);
 var position:u32=0;var valid:Bool=true;
 for symbol in symbols {
  if symbol>255 {valid=false;}
  else {let old=masks.at_or(symbol,0);masks=masks.set(symbol,old | wrapping_shl(1,position));}
  position=position+1;
 }
 if !valid {return None;}
 return Some(Literal{masks:masks.freeze(),accept:wrapping_shl(1,width-1),width:width});
}

fn count_symbols(symbols:List<u32>,masks:List<u32>,accept:u32)->u32 {
 var cursor:Cursor=Cursor{active:0,matches:0};
 for symbol in symbols {cursor=step(cursor,masks.at_or(symbol,0),accept);}
 return cursor.matches;
}
fn octet(word:u32,lane:u32)->u32 {
 return wrapping_shr(word,(lane & 3)*8) & 255;
}
fn packed_step(words:List<u32>,base:u32,word_stride:u32,masks:List<u32>,accept:u32,i:u32,cursor:Cursor)->Cursor {
 let word=words.at_or(base+wrapping_shr(i,2)*word_stride,0);
 let symbol=octet(word,i);
 return step(cursor,masks.at_or(symbol,0),accept);
}

// Explicit physical input: four octets per word. base/stride permit row-major
// and transposed storage with the same algorithm. Index arithmetic wraps as u32;
// applications requiring a nonwrapping address must establish its shape bounds.
fn count_packed<const N:u32>(words:List<u32>,base:u32,word_stride:u32,masks:List<u32>,accept:u32)->u32 {
 return repeat(N,Cursor{active:0,matches:0},fn(i,cursor)=>packed_step(words,base,word_stride,masks,accept,i,cursor)).matches;
}
fn counts_columns<const N:u32>(words:List<u32>,ids:List<u32>,row_count:u32,masks:List<u32>,accept:u32)->List<u32> {
 return ids.map(fn(id)=>count_packed<N>(words,id,row_count,masks,accept));
}
