module ink.knowledge.controlled_folds;
// Ordinary typed authoring algorithms. Their presence grants no equality,
// applicability or profitability authority; canonical proofs are checked afresh.
record FoldInput<T,S> { item:T, accumulated:S, }
record Cursor<S> { value:S, done:Bool, }
record Marked<T> { value:T, eligible:Bool, }
fn any<T>(xs:List<T>,predicate:fn(T)->Bool)->Bool {
 return fold_until(xs,false,fn(x)=>fn(found)=>found,fn(x)=>fn(found)=>found || predicate(x));
}
fn every<T>(xs:List<T>,predicate:fn(T)->Bool)->Bool {
 return fold_until(xs,true,fn(x)=>fn(all)=>!all,fn(x)=>fn(all)=>all && predicate(x));
}
fn fold_mapped_until<A,B,S>(xs:List<A>,initial:S,mapper:fn(A)->B,stop:fn(FoldInput<B,S>)->Bool,step:fn(FoldInput<B,S>)->S)->S {
 return fold_until(xs,initial,fn(x)=>fn(acc)=>stop(FoldInput<B,S>{item:mapper(x),accumulated:acc}),fn(x)=>fn(acc)=>step(FoldInput<B,S>{item:mapper(x),accumulated:acc}));
}
fn fold_filtered_until<T,S>(xs:List<T>,initial:S,predicate:fn(T)->Bool,stop:fn(FoldInput<T,S>)->Bool,step:fn(FoldInput<T,S>)->S)->S {
 return fold_until(xs,initial,fn(x)=>fn(acc)=>predicate(x) && stop(FoldInput<T,S>{item:x,accumulated:acc}),fn(x)=>fn(acc)=>choose(predicate(x),step(FoldInput<T,S>{item:x,accumulated:acc}),acc));
}
// A finite marked-row IR avoids any new stream, pointer or host primitive.
// It is useful authoring data, not a claim that its record allocation is free.
fn mark<T>(xs:List<T>,predicate:fn(T)->Bool)->List<Marked<T>> {
 return xs.map(fn(x)=>Marked<T>{value:x,eligible:predicate(x)});
}
fn scan_marked<T,S>(xs:List<Marked<T>>,initial:S,step:fn(FoldInput<T,S>)->S)->S {
 return foldl(xs,initial,fn(x)=>fn(acc)=>choose(x.eligible,step(FoldInput<T,S>{item:x.value,accumulated:acc}),acc));
}
