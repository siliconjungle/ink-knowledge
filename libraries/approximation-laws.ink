module ink.knowledge.approximation_laws;

law exact_error(x:Int){x-x==0;proof by normalize;}
law translate_error(x:Int,y:Int,k:Int){(x+k)-(y+k)==x-y;proof by normalize;}
law reverse_error(x:Int,y:Int){-(x-y)==y-x;proof by normalize;}
law scaled_error(x:Int,y:Int,k:Int){(x-y)*k==x*k-y*k;proof by normalize;}

law compose_upper(a:Int,b:Int,c:Int,first:Int,second:Int){
 requires ab:a-b<=first;
 requires bc:b-c<=second;
 (a-c<=first+second)==true;
 proof by provided;
}
law compose_lower(a:Int,b:Int,c:Int,first:Int,second:Int){
 requires ab:b-a<=first;
 requires bc:c-b<=second;
 (c-a<=first+second)==true;
 proof by provided;
}
law widen_upper(a:Int,b:Int,small:Int,large:Int){
 requires close:a-b<=small;
 requires wider:small<=large;
 (a-b<=large)==true;
 proof by provided;
}
law widen_lower(a:Int,b:Int,small:Int,large:Int){
 requires close:b-a<=small;
 requires wider:small<=large;
 (b-a<=large)==true;
 proof by provided;
}
law probability_all<T>(space:List<T>){
 count(space.filter(fn(seed)=>true))==count(space);
 proof by induction space;
}
law probability_none<T>(space:List<T>){
 count(space.filter(fn(seed)=>false))==0;
 proof by induction space;
}
law probability_double_complement(space:List<Bool>){
 space.map(fn(seed)=>!seed).map(fn(seed)=>!seed)==space;
 proof by induction space{nil=>normalize;cons(head,tail)=>cases head{true=>normalize;false=>normalize;};};
}
law probability_map<T>(space:List<T>,success:fn(T)->Bool){
 count(space.map(success))==count(space);
 proof by induction space;
}
