module ink.knowledge.incremental_laws;
// External authoring source: the delta rules of incremental (DBSP-style)
// operators, each stated once as a general law in Ink's `law` form and checked
// by the semantic law kernel. A collection with signed multiplicities (a
// Z-set) is a list of elements whose contribution carries its sign, so an
// insertion is a positive element, a removal a negative one, and applying a
// change is appending it. Each law says the operator's output on `old ++ delta`
// is its output on `old` combined with its output on `delta`: maintenance
// costs the size of the change, not of the collection.
fn no_groups() -> Map<u64, Int> { return Map.empty(); }
law group_sum_append<E>(xs: List<E>, ys: List<E>, key: fn(E) -> u64, amount: fn(E) -> Int, k: u64) {
    foldr(xs.concat(ys), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0)
        == foldr(xs, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0)
         + foldr(ys, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0);
    proof by induction xs generalizing (k) {
        nil => normalize;
        cons(h, t) => cases k == key(h) {
            true => assert k == key(h) by hypothesis 0 then calc {
                _ == foldr(t.concat(ys), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(key(h), 0) + amount(h) by normalize;
                  == (foldr(t, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(key(h), 0)
                      + foldr(ys, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(key(h), 0)) + amount(h)
                     by congruence(ih(k = key(h)), normalize);
                  == _ by normalize;
            };
            false => calc {
                _ == foldr(t.concat(ys), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0) by normalize;
                  == _ by ih(k = k);
            };
        };
    };
}

law filter_append<E>(xs: List<E>, ys: List<E>, p: fn(E) -> Bool) {
    xs.concat(ys).filter(p) == xs.filter(p).concat(ys.filter(p));
    proof by induction xs {
        nil => normalize;
        cons(h, t) => cases p(h) { true => normalize; false => normalize; };
    };
}

law sum_split<E>(xs: List<E>, a: fn(E) -> Int, b: fn(E) -> Int) {
    foldr(xs, Int(0), fn(x, acc) => (a(x) + b(x)) + acc) == foldr(xs, Int(0), fn(x, acc) => a(x) + acc) + foldr(xs, Int(0), fn(x, acc) => b(x) + acc);
    proof by induction xs;
}
law sum_append<E>(xs: List<E>, ys: List<E>, a: fn(E) -> Int) {
    foldr(xs.concat(ys), Int(0), fn(x, acc) => a(x) + acc) == foldr(xs, Int(0), fn(x, acc) => a(x) + acc) + foldr(ys, Int(0), fn(x, acc) => a(x) + acc);
    proof by induction xs;
}
law join_sum_append_left<L, R>(xs: List<L>, dxs: List<L>, ys: List<R>, lk: fn(L) -> u64, rk: fn(R) -> u64, w: fn(L, R) -> Int) {
    foldr(xs.concat(dxs), Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
        == foldr(xs, Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
         + foldr(dxs, Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc);
    proof by use sum_append(xs, dxs, fn(x) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a));
}
law join_sum_append_right<L, R>(xs: List<L>, ys: List<R>, dys: List<R>, lk: fn(L) -> u64, rk: fn(R) -> u64, w: fn(L, R) -> Int) {
    foldr(xs, Int(0), fn(x, acc) => foldr(ys.concat(dys), Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
        == foldr(xs, Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
         + foldr(xs, Int(0), fn(x, acc) => foldr(dys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc);
    proof by induction xs {
        nil => normalize;
        cons(h, t) => calc {
            _ == foldr(ys.concat(dys), Int(0), fn(y, a) => choose(lk(h) == rk(y), w(h, y), 0) + a)
                 + (foldr(t, Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
                    + foldr(t, Int(0), fn(x, acc) => foldr(dys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)) by normalize;
              == (foldr(ys, Int(0), fn(y, a) => choose(lk(h) == rk(y), w(h, y), 0) + a) + foldr(dys, Int(0), fn(y, a) => choose(lk(h) == rk(y), w(h, y), 0) + a))
                 + (foldr(t, Int(0), fn(x, acc) => foldr(ys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc)
                    + foldr(t, Int(0), fn(x, acc) => foldr(dys, Int(0), fn(y, a) => choose(lk(x) == rk(y), w(x, y), 0) + a) + acc))
                 by congruence(use sum_append(ys, dys, fn(y) => choose(lk(h) == rk(y), w(h, y), 0)), normalize);
              == _ by normalize;
        };
    };
}

// Views over views: a group-by over a filtered collection. The filter's delta
// rule feeds the group-by's; neither is re-proved.
law filtered_group_sum_append<E>(xs: List<E>, ys: List<E>, p: fn(E) -> Bool, key: fn(E) -> u64, amount: fn(E) -> Int, k: u64) {
    foldr(xs.concat(ys).filter(p), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0)
        == foldr(xs.filter(p), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0)
         + foldr(ys.filter(p), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0);
    proof by calc {
        _ == foldr(xs.filter(p).concat(ys.filter(p)), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + amount(e))).get_or(k, 0)
             by congruence(congruence(use filter_append(xs, ys, p), normalize, normalize), normalize, normalize);
          == _ by use group_sum_append(xs.filter(p), ys.filter(p), key, amount, k);
    };
}
// Counting per key is the group sum of signed multiplicities (count-distinct
// maintains exactly this map; its output changes where a count crosses zero).
law group_count_append<E>(xs: List<E>, ys: List<E>, key: fn(E) -> u64, sign: fn(E) -> Int, k: u64) {
    foldr(xs.concat(ys), no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + sign(e))).get_or(k, 0)
        == foldr(xs, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + sign(e))).get_or(k, 0)
         + foldr(ys, no_groups(), fn(e, m) => m.set(key(e), m.get_or(key(e), 0) + sign(e))).get_or(k, 0);
    proof by use group_sum_append(xs, ys, key, sign, k);
}

// Both inputs can change in one maintenance boundary. The delta-delta term is
// required even when both original inputs are empty. Signed contributions give
// the same equation for insertions, deletions and replacements.
law join_sum_both_deltas<L,R>(xs:List<L>,dx:List<L>,ys:List<R>,dy:List<R>,
 lk:fn(L)->u64,rk:fn(R)->u64,w:fn(L,R)->Int) {
 foldr(xs.concat(dx),Int(0),fn(x,acc)=>foldr(ys.concat(dy),Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
 ==foldr(xs,Int(0),fn(x,acc)=>foldr(ys,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
  +foldr(dx,Int(0),fn(x,acc)=>foldr(ys,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
  +foldr(xs,Int(0),fn(x,acc)=>foldr(dy,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
  +foldr(dx,Int(0),fn(x,acc)=>foldr(dy,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc);
 proof by calc {
  _==foldr(xs,Int(0),fn(x,acc)=>foldr(ys.concat(dy),Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
    +foldr(dx,Int(0),fn(x,acc)=>foldr(ys.concat(dy),Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
   by use join_sum_append_left<L,R>(xs,dx,ys.concat(dy),lk,rk,w);
  ==(foldr(xs,Int(0),fn(x,acc)=>foldr(ys,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
     +foldr(xs,Int(0),fn(x,acc)=>foldr(dy,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc))
    +(foldr(dx,Int(0),fn(x,acc)=>foldr(ys,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc)
     +foldr(dx,Int(0),fn(x,acc)=>foldr(dy,Int(0),fn(y,a)=>choose(lk(x)==rk(y),w(x,y),0)+a)+acc))
   by congruence(use join_sum_append_right<L,R>(xs,ys,dy,lk,rk,w),use join_sum_append_right<L,R>(dx,ys,dy,lk,rk,w));
  ==_ by normalize;
 };
}

law exact_zero_fold<E>(changes:List<E>) {
 foldr(changes,Int(0),fn(item,acc)=>Int(0)+acc)==Int(0);
 proof by induction changes;
}
law weighted_deletion_cancels<E>(changes:List<E>,weight:fn(E)->Int) {
 foldr(changes,Int(0),fn(item,acc)=>weight(item)+acc)
  +foldr(changes,Int(0),fn(item,acc)=>-weight(item)+acc)==Int(0);
 proof by calc {
  _==foldr(changes,Int(0),fn(item,acc)=>(weight(item)+(-weight(item)))+acc)
   by symmetry(use sum_split<E>(changes,weight,fn(item)=>-weight(item)));
  ==foldr(changes,Int(0),fn(item,acc)=>Int(0)+acc) by normalize;
  ==_ by use exact_zero_fold<E>(changes);
 };
}
