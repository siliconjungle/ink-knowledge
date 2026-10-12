module ink.knowledge.contract_algebra;

law choice_true<T>(p:Bool,x:T,y:T){requires known:p;choose(p,x,y)==x;proof by normalize;}

law choice_false<T>(p:Bool,x:T,y:T){requires known:p==false;choose(p,x,y)==y;proof by normalize;}

law choice_same<T>(p:Bool,x:T){choose(p,x,x)==x;proof by normalize;}

law choice_or<T>(p:Bool,q:Bool,x:T,y:T){choose(p,x,choose(q,x,y))==choose(p||q,x,y);proof by cases p{true=>normalize;false=>normalize;};}

law choice_and<T>(p:Bool,q:Bool,x:T,y:T){choose(p,choose(q,x,y),y)==choose(p&&q,x,y);proof by cases p{true=>normalize;false=>normalize;};}

law known_or_choice<T>(p:Bool,q:Bool,x:T,y:T){requires known:p||q;choose(p,x,choose(q,x,y))==x;proof by calc{_==choose(p||q,x,y) by use choice_or<T>(p,q,x,y);==_ by normalize;};}

law known_conjunction_left(p:Bool,q:Bool){requires known:p&&q;p==true;proof by provided;}

law map_count<T,U>(xs:List<T>,f:fn(T)->U){count(xs.map(f))==count(xs);proof by induction xs;}

law count_concat<T>(xs:List<T>,ys:List<T>){count(xs.concat(ys))==count(xs)+count(ys);proof by induction xs;}

law map_known_identity<T>(xs:List<T>,p:Bool){requires known:p;xs.map(fn(x)=>choose(p,x,x))==xs;proof by induction xs;}

law filter_known_true<T>(xs:List<T>,p:Bool){requires known:p;xs.filter(fn(x)=>p)==xs;proof by induction xs;}

law filter_known_false<T>(xs:List<T>,p:Bool){requires known:p==false;xs.filter(fn(x)=>p)==[];proof by induction xs;}

law known_filter_count<T>(xs:List<T>,p:fn(T)->Bool){requires retained:xs.filter(p)==xs;count(xs.filter(p))==count(xs);proof by normalize;}

law zero_count_map<T,U>(xs:List<T>,f:fn(T)->U){requires empty:count(xs)==0;count(xs.map(f))==0;proof by calc{_==count(xs) by use map_count<T,U>(xs,f);==_ by hypothesis empty;};}

law known_same_map<T,U>(xs:List<T>,ys:List<T>,f:fn(T)->U){requires same:xs==ys;xs.map(f)==ys.map(f);proof by normalize;}

law known_same_filter<T>(xs:List<T>,ys:List<T>,p:fn(T)->Bool){requires same:xs==ys;xs.filter(p)==ys.filter(p);proof by normalize;}

law known_same_count<T>(xs:List<T>,ys:List<T>){requires same:xs==ys;count(xs)==count(ys);proof by normalize;}

law bag_reflexive<T>(xs:List<T>){(multiset(xs)==multiset(xs))==true;proof by induction xs;}

law map_identity<T>(xs:List<T>){xs.map(fn(x)=>x)==xs;proof by induction xs;}

law bag_identity_map<T>(xs:List<T>){(multiset(xs.map(fn(x)=>x))==multiset(xs))==true;proof by calc{_==(multiset(xs)==multiset(xs)) by congruence(normalize,use map_identity<T>(xs));==_ by use bag_reflexive<T>(xs);};}

law occurrences_concat<T>(xs:List<T>,ys:List<T>,item:T){count(xs.concat(ys).filter(fn(x)=>list(x)==list(item)))==count(xs.filter(fn(x)=>list(x)==list(item)))+count(ys.filter(fn(x)=>list(x)==list(item)));proof by induction xs{nil=>normalize;cons(head,tail)=>cases list(head)==list(item){true=>normalize;false=>normalize;};};}

law map_scale_zero_u32(xs:List<u32>,k:u32){requires known:k==0;xs.map(fn(x)=>x*k)==xs.map(fn(x)=>0);proof by induction xs;}

law map_scale_one_u32(xs:List<u32>,k:u32){requires known:k==1;xs.map(fn(x)=>x*k)==xs;proof by induction xs;}

law sum_scale_zero_u32(xs:List<u32>,k:u32){requires known:k==0;sum(xs.map(fn(x)=>x*k))==0;proof by induction xs;}

law retained_filter_sum_u32(xs:List<u32>,p:fn(u32)->Bool){requires retained:xs.filter(p)==xs;sum(xs.filter(p))==sum(xs);proof by normalize;}

law map_scale_zero_u64(xs:List<u64>,k:u64){requires known:k==0;xs.map(fn(x)=>x*k)==xs.map(fn(x)=>0);proof by induction xs;}

law map_scale_one_u64(xs:List<u64>,k:u64){requires known:k==1;xs.map(fn(x)=>x*k)==xs;proof by induction xs;}

law sum_scale_zero_u64(xs:List<u64>,k:u64){requires known:k==0;sum(xs.map(fn(x)=>x*k))==0;proof by induction xs;}

law retained_filter_sum_u64(xs:List<u64>,p:fn(u64)->Bool){requires retained:xs.filter(p)==xs;sum(xs.filter(p))==sum(xs);proof by normalize;}

law map_scale_zero_i32(xs:List<i32>,k:i32){requires known:k==0;xs.map(fn(x)=>x*k)==xs.map(fn(x)=>0);proof by induction xs;}

law map_scale_one_i32(xs:List<i32>,k:i32){requires known:k==1;xs.map(fn(x)=>x*k)==xs;proof by induction xs;}

law sum_scale_zero_i32(xs:List<i32>,k:i32){requires known:k==0;sum(xs.map(fn(x)=>x*k))==0;proof by induction xs;}

law retained_filter_sum_i32(xs:List<i32>,p:fn(i32)->Bool){requires retained:xs.filter(p)==xs;sum(xs.filter(p))==sum(xs);proof by normalize;}

law map_scale_zero_int(xs:List<Int>,k:Int){requires known:k==0;xs.map(fn(x)=>x*k)==xs.map(fn(x)=>0);proof by induction xs;}

law map_scale_one_int(xs:List<Int>,k:Int){requires known:k==1;xs.map(fn(x)=>x*k)==xs;proof by induction xs;}

law sum_scale_zero_int(xs:List<Int>,k:Int){requires known:k==0;sum(xs.map(fn(x)=>x*k))==0;proof by induction xs;}

law retained_filter_sum_int(xs:List<Int>,p:fn(Int)->Bool){requires retained:xs.filter(p)==xs;sum(xs.filter(p))==sum(xs);proof by normalize;}

law sorted_count_u32(xs:List<u32>){requires sorted:xs.sort()==xs;count(xs.sort())==count(xs);proof by normalize;}

law sorted_sum_u32(xs:List<u32>){requires sorted:xs.sort()==xs;sum(xs.sort())==sum(xs);proof by normalize;}

law sorted_map_u32(xs:List<u32>,f:fn(u32)->u32){requires sorted:xs.sort()==xs;xs.sort().map(f)==xs.map(f);proof by normalize;}

law sorted_again_u32(xs:List<u32>){requires sorted:xs.sort()==xs;xs.sort().sort()==xs;proof by normalize;}

law sorted_count_u64(xs:List<u64>){requires sorted:xs.sort()==xs;count(xs.sort())==count(xs);proof by normalize;}

law sorted_sum_u64(xs:List<u64>){requires sorted:xs.sort()==xs;sum(xs.sort())==sum(xs);proof by normalize;}

law sorted_map_u64(xs:List<u64>,f:fn(u64)->u64){requires sorted:xs.sort()==xs;xs.sort().map(f)==xs.map(f);proof by normalize;}

law sorted_again_u64(xs:List<u64>){requires sorted:xs.sort()==xs;xs.sort().sort()==xs;proof by normalize;}

law sorted_count_i32(xs:List<i32>){requires sorted:xs.sort()==xs;count(xs.sort())==count(xs);proof by normalize;}

law sorted_sum_i32(xs:List<i32>){requires sorted:xs.sort()==xs;sum(xs.sort())==sum(xs);proof by normalize;}

law sorted_map_i32(xs:List<i32>,f:fn(i32)->i32){requires sorted:xs.sort()==xs;xs.sort().map(f)==xs.map(f);proof by normalize;}

law sorted_again_i32(xs:List<i32>){requires sorted:xs.sort()==xs;xs.sort().sort()==xs;proof by normalize;}

law integer_add_same(a:Int,b:Int,k:Int){requires same:a==b;a+k==b+k;proof by normalize;}

law integer_subtract_same(a:Int,b:Int,k:Int){requires same:a==b;a-k==b-k;proof by normalize;}

law integer_multiply_same(a:Int,b:Int,k:Int){requires same:a==b;a*k==b*k;proof by normalize;}

law integer_bound_transitive(a:Int,b:Int,c:Int){requires first:a<=b;requires second:b<=c;(a<=c)==true;proof by provided;}

law integer_strict_predecessor(n:Int){(n-1<n)==true;proof by provided;}

law integer_positive_zero(n:Int){requires positive:n>0;(0<n)==true;proof by provided;}

law count_nonnegative<T>(xs:List<T>){(count(xs)>=0)==true;proof by provided;}

law filter_count_bound<T>(xs:List<T>,p:fn(T)->Bool){(count(xs.filter(p))<=count(xs))==true;proof by provided;}

law count_filter_false<T>(xs:List<T>){count(xs.filter(fn(x)=>false))==0;proof by induction xs;}

law count_filter_true<T>(xs:List<T>){count(xs.filter(fn(x)=>true))==count(xs);proof by induction xs;}
