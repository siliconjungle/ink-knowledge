module ink.knowledge.buffer_view_laws;

// Fixed borrow semantics expose a logical list slice, without granting a
// source callback mutation or ownership of that slice.
law range_at<T>(owner:Buffer<T>,start:u32,count:u32,index:u32,fallback:T){
 owner.borrow_range(start,count,fn(view)=>view.at_or(index,fallback))
  ==owner.freeze().drop(start).take(count).at_or(index,fallback);
}
law range_length<T>(owner:Buffer<T>,start:u32,count:u32){
 owner.borrow_range(start,count,fn(view)=>view.len())
  ==length(owner.freeze().drop(start).take(count));
}
law nested_range<T>(owner:Buffer<T>,start:u32,count:u32,inner_start:u32,inner_count:u32,index:u32,fallback:T){
 owner.borrow_range(start,count,fn(view)=>view.borrow_range(inner_start,inner_count,fn(inner)=>inner.at_or(index,fallback)))
  ==owner.freeze().drop(start).take(count).drop(inner_start).take(inner_count).at_or(index,fallback);
}
