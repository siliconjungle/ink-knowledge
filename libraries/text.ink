module ink.knowledge.text;
// Chunked text is ordinary immutable data. Slicing addresses UTF-8 bytes;
// callers never get a malformed String from a split code point.
record Text { chunks:List<String>, }
pub fn empty()->Text{return Text{chunks:[]};}
pub fn from_string(s:String)->Text{return Text{chunks:[s]};}
pub fn append(a:Text,b:Text)->Text{return Text{chunks:a.chunks.concat(b.chunks)};}
pub fn byte_length(t:Text)->Option<u32>{return foldl(t.chunks,Some(0),fn(s)=>fn(acc)=>acc.fold(fn(n)=>choose(n+string_byte_len(s)<n,None,Some(n+string_byte_len(s))),fn(u)=>None));}
pub fn flatten(t:Text)->String{return foldl(t.chunks,"",fn(s)=>fn(acc)=>string_concat(acc,s));}
pub fn slice(t:Text,start:u32,end:u32)->Option<String>{return string_slice(flatten(t),start,end);}
pub fn find(t:Text,needle:String,start:u32)->Option<u32>{return string_find(flatten(t),needle,start);}
pub fn insert(t:Text,at:u32,value:String)->Option<Text>{
 let s:String=flatten(t);let n:u32=string_byte_len(s);
 return string_slice(s,0,at).fold(fn(a)=>string_slice(s,at,n).map(fn(b)=>Text{chunks:[a,value,b]}),fn(u)=>None);
}
