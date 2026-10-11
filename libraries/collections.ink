module ink.knowledge.collections;

// Stable, deterministic observable order. Algorithms are ordinary library
// definitions; the compiler has no set, grouping or join algorithm cases.
type Set<T> = List<T>;
record Entry<K,V> { key:K, value:V, }
record Group<K,V> { key:K, values:List<V>, }
record Joined<K,A,B> { key:K, left:A, right:B, }

fn contains<T>(xs:List<T>,value:T)->Bool {
    return foldl(xs,false,fn(x)=>fn(found)=>found || x==value);
}
fn set<T>(xs:List<T>)->Set<T> {
    var output:List<T>=[];
    for x in xs { if !contains<T>(output,x) {output=output.concat([x]);} }
    return output;
}
fn union<T>(a:Set<T>,b:Set<T>)->Set<T> {return set<T>(a.concat(b));}
fn intersection<T>(a:Set<T>,b:Set<T>)->Set<T> {return set<T>(a.filter(fn(x)=>contains<T>(b,x)));}
fn difference<T>(a:Set<T>,b:Set<T>)->Set<T> {return set<T>(a.filter(fn(x)=>!contains<T>(b,x)));}
fn map<T,U>(xs:List<T>,f:fn(T)->U)->List<U> {return xs.map(f);}
fn filter<T>(xs:List<T>,predicate:fn(T)->Bool)->List<T> {return xs.filter(predicate);}
record FoldState<T,U> { item:T, accumulated:U, }
fn reduce<T,U>(xs:List<T>,initial:U,step:fn(FoldState<T,U>)->U)->U {
    var accumulated:U=initial;
    for item in xs {accumulated=step(FoldState<T,U>{item:item,accumulated:accumulated});}
    return accumulated;
}

// Groups follow the first appearance of a key; rows within each group retain
// input order. K uses the general owned-map key contract.
fn group<K,V>(rows:List<Entry<K,V>>)->List<Group<K,V>> {
    var buckets:Map<K,List<V>>=Map.empty();
    var order:Buffer<K>=Buffer.empty();
    for row in rows {
        if !buckets.contains(row.key) {order=order.push(row.key);}
        let previous:List<V>=buckets.get_or(row.key,[]);
        buckets=buckets.set(row.key,previous.concat([row.value]));
    }
    let order=order.freeze();
    var output:Buffer<Group<K,V>>=Buffer.empty();
    for key in order {output=output.push(Group<K,V>{key:key,values:buckets.get_or(key,[])});}
    return output.freeze();
}
// Left-major, then right-major order. Duplicates produce their full Cartesian
// product; key equality is ordinary structural equality.
fn join<K,A,B>(left:List<Entry<K,A>>,right:List<Entry<K,B>>)->List<Joined<K,A,B>> {
    var output:Buffer<Joined<K,A,B>>=Buffer.empty();
    for a in left {for b in right {
        if a.key==b.key {output=output.push(Joined<K,A,B>{key:a.key,left:a.value,right:b.value});}
    }}
    return output.freeze();
}

// Disjoint scoped owners are general execution machinery. This reusable
// partition algorithm stays in knowledge and retains input order.
fn partition_map<T>(xs:List<T>,at:u32,left:fn(T)->T,right:fn(T)->T)->List<T>{
 return buffer(xs).split_at(at,fn(a)=>fn(b)=>a.map(left).append(b.map(right))).freeze();
}

// An alternative for joins with many distinct right-hand keys. Buckets retain
// right input order and every duplicate; the outer traversal retains left order.
// Bucket construction and copying costs belong in lifecycle measurements.
fn join_indexed<K,A,B>(left:List<Entry<K,A>>,right:List<Entry<K,B>>)->List<Joined<K,A,B>> {
    var buckets:Map<K,List<B>>=Map.empty();
    for row in right {
        let previous:List<B>=buckets.get_or(row.key,[]);
        buckets=buckets.set(row.key,previous.concat([row.value]));
    }
    var output:Buffer<Joined<K,A,B>>=Buffer.empty();
    for row in left {
        let matches:List<B>=buckets.get_or(row.key,[]);
        for value in matches {
            output=output.push(Joined<K,A,B>{key:row.key,left:row.value,right:value});
        }
    }
    return output.freeze();
}

// Fold two observations in one left-to-right traversal. Each accumulator keeps
// its own exact source order; no reassociation is needed.
record Totals<A,B> { first:A, second:B, }
fn reduce_pair<T,A,B>(rows:List<T>,initial:Totals<A,B>,first:fn(FoldState<T,A>)->A,second:fn(FoldState<T,B>)->B)->Totals<A,B> {
    var totals:Totals<A,B>=initial;
    for item in rows {
        totals=Totals<A,B>{first:first(FoldState<T,A>{item:item,accumulated:totals.first}),second:second(FoldState<T,B>{item:item,accumulated:totals.second})};
    }
    return totals;
}

// Stable bounded insertion order. less receives a Comparison record and is a strict ordering predicate;
// equal entries retain input order. Work/storage depend on k, not full sorting.
// k=0 and k above the row count have ordinary total semantics.
record Comparison<T>{left:T,right:T,}
fn top_k<T>(rows:List<T>,k:u32,less:fn(Comparison<T>)->Bool)->List<T> {
    if k==0 {return [];}
    var best:List<T>=[];
    for row in rows {
        var output:Buffer<T>=Buffer.empty();
        var inserted:Bool=false;
        for candidate in best {
            if !inserted && less(Comparison<T>{left:row,right:candidate}) {
                if output.len()<k {output=output.push(row);}
                inserted=true;
            }
            if output.len()<k {output=output.push(candidate);}
        }
        if !inserted && output.len()<k {output=output.push(row);}
        best=output.freeze();
    }
    return best;
}

// Maintain two ordered accumulators per group in one traversal, without
// materialising the group row lists. Output follows first key appearance.
record GroupTotals<K,A,B>{key:K,totals:Totals<A,B>,}
fn reduce_pair_by<K,T,A,B>(rows:List<Entry<K,T>>,initial:Totals<A,B>,first:fn(FoldState<T,A>)->A,second:fn(FoldState<T,B>)->B)->List<GroupTotals<K,A,B>> {
    var totals:Map<K,Totals<A,B>>=Map.empty();
    var order:Buffer<K>=Buffer.empty();
    for row in rows {
        if !totals.contains(row.key) {order=order.push(row.key);}
        let old=totals.get_or(row.key,initial);
        totals=totals.set(row.key,Totals<A,B>{first:first(FoldState<T,A>{item:row.value,accumulated:old.first}),second:second(FoldState<T,B>{item:row.value,accumulated:old.second})});
    }
    let order=order.freeze();
    var output:Buffer<GroupTotals<K,A,B>>=Buffer.empty();
    for key in order {output=output.push(GroupTotals<K,A,B>{key:key,totals:totals.get_or(key,initial)});}
    return output.freeze();
}
