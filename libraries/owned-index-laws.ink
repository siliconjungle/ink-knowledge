module ink.knowledge.owned_index_laws;

// A covering index suffices to prove that an absent key is absent from the
// logical prefix. The implication is guarded so its induction hypothesis
// remains valid for every tail, including prefixes that are not covered.
law absent_from_covered_u32(xs:List<u32>,seen:Map<u32,Bool>,item:u32){
 choose(foldr(xs,true,fn(x,ok)=>seen.contains(x)&&ok)&&!seen.contains(item),
  foldr(xs,false,fn(x,found)=>[x]==[item]||found)==false,true)==true;
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>cases seen.contains(item){
   true=>cases foldr([head].concat(tail),true,fn(x,ok)=>seen.contains(x)&&ok){true=>normalize;false=>normalize;};
   false=>cases seen.contains(head){
    false=>normalize;
    true=>cases head==item{
     true=>assert head==item by hypothesis 3 then
      assert false==true by calc{
       _==seen.contains(item) by normalize;
       ==seen.contains(head) by congruence(normalize,normalize);
       ==_ by hypothesis 2;
      } then normalize;
     false=>ih;
    };
   };
  };
 };
}

law coverage_insert_u32(xs:List<u32>,seen:Map<u32,Bool>,item:u32){
 choose(foldr(xs,true,fn(x,ok)=>seen.contains(x)&&ok),
  foldr(xs,true,fn(x,ok)=>seen.set(item,true).contains(x)&&ok),true)==true;
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>cases seen.contains(head){
   false=>normalize;
   true=>cases head==item{true=>ih;false=>ih;};
  };
 };
}

law coverage_append_u32(xs:List<u32>,seen:Map<u32,Bool>,item:u32){
 foldr(xs.concat([item]),true,fn(x,ok)=>seen.set(item,true).contains(x)&&ok)
 ==foldr(xs,true,fn(x,ok)=>seen.set(item,true).contains(x)&&ok);
 proof by induction xs{nil=>normalize;cons(head,tail)=>normalize;};
}
