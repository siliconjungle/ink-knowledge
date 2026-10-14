module ink.knowledge.buffer_views;

// Algorithms stay ordinary library source. The scoped callback lends a clipped
// range; it cannot mutate an owner or let the view escape.
fn at<T>(items:List<T>,start:u32,count:u32,index:u32,fallback:T)->T {
 let owner=buffer(items);
 return owner.borrow_range(start,count,fn(view)=>view.at_or(index,fallback));
}
fn sum_window(items:List<u32>,start:u32,count:u32)->u32 {
 let owner=buffer(items);
 return owner.borrow_range(start,count,fn(view)=>
  repeat_until(view.len(),0,fn(total)=>false,fn(i)=>fn(total)=>total+view.at_or(i,0)));
}
