module ink.knowledge.frame_laws;
// An observer can be moved outside traversal only after every step has proved
// preservation. Concrete source instances must discharge that obligation.
law fold_frame<A,S,R>(xs:List<A>,state:S,observe:fn(S)->R,step:fn(A,S)->S){
 assume preserved(item:A,current:S): observe(step(item,current))==observe(current);
 observe(foldl(xs,state,step))==observe(state);
 proof by induction xs generalizing(state){
  nil=>normalize;
  cons(head,tail)=>calc{
   _ == observe(step(head,state)) by ih(state=step(head,state));
     == _ by assumption preserved(head,state);
  };
 };
}
record Cursor{data:List<u32>,index:u32,}
law cursor_data(xs:List<u32>,data:List<u32>,index:u32){
 foldl(xs,Cursor{data:data,index:index},fn(value,c)=>Cursor{data:c.data,index:c.index+value}).data==data;
 proof by use fold_frame<u32,Cursor,List<u32>>(xs,Cursor{data:data,index:index},fn(c)=>c.data,fn(value,c)=>Cursor{data:c.data,index:c.index+value})
  assuming(normalize);
}
