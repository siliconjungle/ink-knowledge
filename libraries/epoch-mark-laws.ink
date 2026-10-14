module epoch_mark_laws;
record ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:u32,flag:u32,}
law fresh(mark:ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b,generation:u32){
 requires current: (mark.epoch==generation)==true;
 choose(mark.epoch==generation,mark.flag,0)==mark.flag;
}
law stale(mark:ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b,generation:u32){
 requires other: (mark.epoch==generation)==false;
 choose(mark.epoch==generation,mark.flag,0)==0;
}
law written_current(generation:u32,value:u32){
 choose(ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:generation,flag:value}.epoch==generation,ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:generation,flag:value}.flag,0)==value;
}
law empty_any_generation(generation:u32){
 choose(ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:0,flag:0}.epoch==generation,ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:0,flag:0}.flag,0)==0;
 proof by cases 0==generation {true=>normalize;false=>normalize;};
}
law reset_decoded(marks:List<ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b>,generation:u32){
 buffer(marks).map(fn(mark)=>ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b{epoch:0,flag:0}).freeze().map(fn(mark)=>choose(mark.epoch==generation,mark.flag,0))
  ==marks.map(fn(mark)=>0);
 proof by induction marks {
  nil=>normalize;
  cons(head,tail)=>cases 0==generation {true=>normalize;false=>normalize;};
 };
}
law map_append<T,U>(xs:List<T>,ys:List<T>,f:fn(T)->U){
 xs.concat(ys).map(f)==xs.map(f).concat(ys.map(f));
 proof by induction xs;
}
law push_decoded(buffer:Buffer<ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b>,mark:ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b,generation:u32){
 buffer.push(mark).freeze().map(fn(mark)=>choose(mark.epoch==generation,mark.flag,0))
  ==buffer.freeze().map(fn(mark)=>choose(mark.epoch==generation,mark.flag,0)).concat([choose(mark.epoch==generation,mark.flag,0)]);
 proof by use map_append<ink_m7495e1b64b54b10ef593154282193e3b52cce997ecfda3aa665924a49bb4661b,u32>(buffer.freeze(),[mark],fn(mark)=>choose(mark.epoch==generation,mark.flag,0));
}
