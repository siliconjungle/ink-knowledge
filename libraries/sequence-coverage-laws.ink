module ink.knowledge.sequence_coverage_laws;

law covered_witness_u32(xs:List<u32>,item:u32,p:fn(u32)->Bool){
 choose(foldr(xs,true,fn(x,ok)=>p(x)&&ok),
  choose(foldr(xs,false,fn(x,found)=>item==x||found),p(item),true),true)==true;
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>cases p(head){
   false=>normalize;
   true=>cases item==head{
    true=>assert item==head by hypothesis 2 then normalize;
    false=>ih;
   };
  };
 };
}

law all_monotone<A>(xs:List<A>,p:fn(A)->Bool,q:fn(A)->Bool){
 assume implies(item:A) requires p(item):q(item)==true;
 choose(foldr(xs,true,fn(x,ok)=>p(x)&&ok),foldr(xs,true,fn(x,ok)=>q(x)&&ok),true)==true;
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>cases p(head){
   false=>normalize;
   true=>cases q(head){
    true=>ih;
    false=>cases foldr(tail,true,fn(x,ok)=>p(x)&&ok){
     false=>normalize;
     true=>calc{_==q(head) by normalize;==_ by assumption implies(head);};
    };
   };
  };
 };
}

law member_append_u32(xs:List<u32>,added:u32,key:u32){
 foldr(xs.concat([added]),false,fn(x,found)=>key==x||found)
 ==(key==added||foldr(xs,false,fn(x,found)=>key==x||found));
 proof by induction xs{nil=>normalize;cons(head,tail)=>cases key==head{true=>cases key==added{true=>normalize;false=>normalize;};false=>ih;};};
}
