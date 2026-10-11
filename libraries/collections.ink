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
