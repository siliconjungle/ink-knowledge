module ink.knowledge.contract_laws;
// These observations are the same exact computations as source contracts.
record Job{id:u32,value:u32,}
law zero_map(xs:List<u64>){
  sum(xs.map(fn(x)=>x*0)) == 0;
  proof by induction xs;
}
law identity_map(xs:List<u32>){
  xs.map(fn(x)=>x+0) == xs;
  proof by induction xs;
}
law sorted_identity(xs:List<u64>){
  requires ordered: xs.sort()==xs;
  xs.sort()==xs;
  proof by hypothesis ordered;
}
law unique_id_check_erasure(xs:List<Job>){
  requires known: unique_ids(xs);
  unique_ids(xs)==true;
  proof by hypothesis known;
}
law bag_multiplicity(){
  (multiset(list(1,2,1))==multiset(list(2,1))+singleton(1)) == true;
}
law bag_condition(){
  requires same: multiset(list(1,2))==multiset(list(2,1));
  true==true;
}
