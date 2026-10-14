module ink.knowledge.small_sequence;

// A small immutable sequence. The first two values stay in scalar fields;
// promotion retains the complete list. No kind/count assumption is required
// for the logical view: every other kind uses `many`.
record Small<T>{kind:u32,first:T,second:T,many:List<T>,}
fn empty<T>(fallback:T)->Small<T>{return Small<T>{kind:0,first:fallback,second:fallback,many:[]};}
fn view<T>(s:Small<T>)->List<T>{
 if s.kind==0{return [];}
 if s.kind==1{return [s.first];}
 if s.kind==2{return [s.first,s.second];}
 return s.many;
}
fn push<T>(s:Small<T>,value:T)->Small<T>{
 if s.kind==0{return Small<T>{..s,kind:1,first:value};}
 if s.kind==1{return Small<T>{..s,kind:2,second:value};}
 if s.kind==2{return Small<T>{..s,kind:3,many:[s.first,s.second,value]};}
 return Small<T>{..s,kind:3,many:buffer(s.many).push(value).freeze()};
}
fn encoded<T>(xs:List<T>,fallback:T)->Small<T>{return foldl(xs,empty<T>(fallback),fn(value,s)=>push<T>(s,value));}
fn length_of<T>(s:Small<T>)->u32{return choose(s.kind<=2,s.kind,length(s.many));}
