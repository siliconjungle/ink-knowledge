module ink.knowledge.indexed_sequence_laws;
// Fixed scalar keys use the existing affine map capability. Algorithms and
// their proof closures are database source, with no privileged compiler case.
fn index_u32(xs:List<u32>)->Map<u32,Bool>{
 return foldr(xs,Map.empty(),fn(item)=>fn(seen)=>seen.set(item,true));
}
fn intersection_indexed_u32(xs:List<u32>,ys:List<u32>)->List<u32>{
 let seen:Map<u32,Bool>=index_u32(ys);
 return xs.filter(fn(item)=>seen.contains(item));
}
fn difference_indexed_u32(xs:List<u32>,ys:List<u32>)->List<u32>{
 let seen:Map<u32,Bool>=index_u32(ys);
 return xs.filter(fn(item)=>!seen.contains(item));
}

law indexed_membership_u32(xs:List<u32>,item:u32){
 index_u32(xs).contains(item)==foldr(xs,false,fn(x,found)=>item==x||found);
 proof by induction xs{nil=>normalize;cons(head,tail)=>cases item==head{true=>normalize;false=>ih;};};
}
law word_equal_symmetric(a:u32,b:u32){
 (a==b)==(b==a);
 proof by cases a==b{
  true=>assert a==b by hypothesis 0 then normalize;
  false=>cases b==a{true=>assert b==a by hypothesis 1 then normalize;false=>normalize;};
 };
}
law word_identity_u32(a:u32,b:u32){
 ([a]==[b])==(b==a);
 proof by calc{_==(a==b) by normalize;==_ by use word_equal_symmetric(a,b);};
}
law membership_direction_u32(xs:List<u32>,item:u32){
 foldr(xs,false,fn(x,found)=>item==x||found)
 ==foldr(xs,false,fn(x,found)=>[x]==[item]||found);
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>calc{
   _==(item==head)||foldr(tail,false,fn(x,found)=>item==x||found) by normalize;
   ==([head]==[item])||foldr(tail,false,fn(x,found)=>[x]==[item]||found)
     by congruence(symmetry(use word_identity_u32(head,item)),ih);
   ==_ by normalize;
  };
 };
}
law structural_indexed_membership_u32(xs:List<u32>,item:u32){
 index_u32(xs).contains(item)==foldr(xs,false,fn(x,found)=>[x]==[item]||found);
 proof by calc{
  _==foldr(xs,false,fn(x,found)=>item==x||found) by use indexed_membership_u32(xs,item);
  ==_ by use membership_direction_u32(xs,item);
 };
}
law indexed_intersection_u32(xs:List<u32>,ys:List<u32>){
 intersection_indexed_u32(xs,ys)
 ==xs.filter(fn(item)=>foldr(ys,false,fn(x,found)=>[x]==[item]||found));
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>calc{
   _==choose(index_u32(ys).contains(head),[head].concat(intersection_indexed_u32(tail,ys)),intersection_indexed_u32(tail,ys)) by normalize;
   ==choose(foldr(ys,false,fn(x,found)=>[x]==[head]||found),[head].concat(tail.filter(fn(item)=>foldr(ys,false,fn(x,found)=>[x]==[item]||found))),tail.filter(fn(item)=>foldr(ys,false,fn(x,found)=>[x]==[item]||found)))
     by congruence(use structural_indexed_membership_u32(ys,head),congruence(normalize,ih),ih);
   ==_ by normalize;
  };
 };
}
law indexed_difference_u32(xs:List<u32>,ys:List<u32>){
 difference_indexed_u32(xs,ys)
 ==xs.filter(fn(item)=>!foldr(ys,false,fn(x,found)=>[x]==[item]||found));
 proof by induction xs{
  nil=>normalize;
  cons(head,tail)=>calc{
   _==choose(!index_u32(ys).contains(head),[head].concat(difference_indexed_u32(tail,ys)),difference_indexed_u32(tail,ys)) by normalize;
   ==choose(!foldr(ys,false,fn(x,found)=>[x]==[head]||found),[head].concat(tail.filter(fn(item)=>!foldr(ys,false,fn(x,found)=>[x]==[item]||found))),tail.filter(fn(item)=>!foldr(ys,false,fn(x,found)=>[x]==[item]||found)))
     by congruence(congruence(use structural_indexed_membership_u32(ys,head),normalize),congruence(normalize,ih),ih);
   ==_ by normalize;
  };
 };
}
