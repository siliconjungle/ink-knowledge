module ink.knowledge.general_laws;
// External authoring source: general laws in Ink's one `law` form, checked by
// the semantic law kernel (`ink emit-laws`). These declarations are not
// executable application syntax and cannot silently enable a rewrite. Type
// parameters are opaque while a law is proved; a general law reaches a program
// only through a concrete law that uses it (proving its assumptions).

record Point { x: u32, y: u32, }

// ---------------------------------------------------------------- lists ----

law map_identity<A>(xs: List<A>) {
    xs.map(fn(x) => x) == xs;
    proof by induction xs;
}
law map_fusion<A, B, C>(xs: List<A>, f: fn(A) -> B, g: fn(B) -> C) {
    xs.map(f).map(g) == xs.map(fn(x) => g(f(x)));
    proof by induction xs;
}
law filter_fusion<A>(xs: List<A>, p: fn(A) -> Bool, q: fn(A) -> Bool) {
    xs.filter(p).filter(q) == xs.filter(fn(x) => p(x) && q(x));
    proof by induction xs {
        nil => normalize;
        cons(h, t) => cases p(h) {
            true => cases q(h) { true => normalize; false => normalize; };
            false => normalize;
        };
    };
}
law map_append<A, B>(xs: List<A>, ys: List<A>, f: fn(A) -> B) {
    xs.concat(ys).map(f) == xs.map(f).concat(ys.map(f));
    proof by induction xs;
}
law filter_append<A>(xs: List<A>, ys: List<A>, p: fn(A) -> Bool) {
    xs.concat(ys).filter(p) == xs.filter(p).concat(ys.filter(p));
    proof by induction xs {
        nil => normalize;
        cons(h, t) => cases p(h) { true => normalize; false => normalize; };
    };
}
law concat_associates<A>(xs: List<A>, ys: List<A>, zs: List<A>) {
    xs.concat(ys).concat(zs) == xs.concat(ys.concat(zs));
    proof by induction xs;
}
law concat_empty<A>(xs: List<A>) {
    xs.concat([]) == xs;
    proof by induction xs;
}
law length_map<A, B>(xs: List<A>, f: fn(A) -> B) {
    length(xs.map(f)) == length(xs);
    proof by induction xs;
}
law length_append<A>(xs: List<A>, ys: List<A>) {
    length(xs.concat(ys)) == length(xs) + length(ys);
    proof by induction xs;
}
// ---------------------------------------------- folds (any monoid) ----

law foldr_map<A, B, S>(xs: List<A>, f: fn(A) -> B, init: S, step: fn(B, S) -> S) {
    foldr(xs.map(f), init, fn(y, acc) => step(y, acc)) == foldr(xs, init, fn(x, acc) => step(f(x), acc));
    proof by induction xs;
}
law foldl_append<A, S>(xs: List<A>, ys: List<A>, s: S, f: fn(S, A) -> S) {
    foldl(xs.concat(ys), s, fn(x, acc) => f(acc, x))
        == foldl(ys, foldl(xs, s, fn(x, acc) => f(acc, x)), fn(x, acc) => f(acc, x));
    proof by induction xs generalizing (s) {
        nil => normalize;
        cons(h, t) => ih(s = f(s, h));
    };
}
// The first-order library's sum_filter: dropped elements weigh zero.
law fold_filter<A, M>(xs: List<A>, p: fn(A) -> Bool, w: fn(A) -> M, zero: M, plus: fn(M, M) -> M) {
    assume zero_left(a: M): plus(zero, a) == a;
    foldr(xs.filter(p), zero, fn(x, acc) => plus(w(x), acc))
        == foldr(xs, zero, fn(x, acc) => plus(choose(p(x), w(x), zero), acc));
    proof by induction xs {
        nil => normalize;
        cons(h, t) => cases p(h) {
            true => normalize;
            false => calc {
                _ == foldr(t, zero, fn(x, acc) => plus(choose(p(x), w(x), zero), acc)) by normalize;
                  == _ by symmetry(assumption zero_left(foldr(t, zero, fn(x, acc) => plus(choose(p(x), w(x), zero), acc))));
            };
        };
    };
}
// The first-order library's sum_congruence: pointwise-equal weights.
law fold_congruence<A, M>(xs: List<A>, w: fn(A) -> M, v: fn(A) -> M, zero: M, plus: fn(M, M) -> M) {
    assume agree(x: A): w(x) == v(x);
    foldr(xs, zero, fn(x, acc) => plus(w(x), acc)) == foldr(xs, zero, fn(x, acc) => plus(v(x), acc));
    proof by induction xs {
        nil => normalize;
        cons(h, t) => calc {
            _ == plus(w(h), foldr(t, zero, fn(x, acc) => plus(v(x), acc))) by normalize;
              == plus(v(h), foldr(t, zero, fn(x, acc) => plus(v(x), acc)))
                 by congruence(congruence(normalize, assumption agree(h)), normalize);
              == _ by normalize;
        };
    };
}
// The first-order library's sum_append, for any monoid.
law fold_append<A, M>(xs: List<A>, ys: List<A>, w: fn(A) -> M, zero: M, plus: fn(M, M) -> M) {
    assume zero_left(a: M): plus(zero, a) == a;
    assume associates(a: M, b: M, c: M): plus(plus(a, b), c) == plus(a, plus(b, c));
    foldr(xs.concat(ys), zero, fn(x, acc) => plus(w(x), acc))
        == plus(foldr(xs, zero, fn(x, acc) => plus(w(x), acc)), foldr(ys, zero, fn(x, acc) => plus(w(x), acc)));
    proof by induction xs {
        nil => symmetry(assumption zero_left(foldr(ys, zero, fn(x, acc) => plus(w(x), acc))));
        cons(h, t) => calc {
            _ == plus(w(h), plus(foldr(t, zero, fn(x, acc) => plus(w(x), acc)), foldr(ys, zero, fn(x, acc) => plus(w(x), acc)))) by normalize;
              == _ by symmetry(assumption associates(w(h), foldr(t, zero, fn(x, acc) => plus(w(x), acc)), foldr(ys, zero, fn(x, acc) => plus(w(x), acc))));
        };
    };
}
// Instances: word sums and counts. Their monoid assumptions hold by computation.
law sum_append_u64(xs: List<u64>, ys: List<u64>) {
    foldr(xs.concat(ys), 0, fn(x, acc) => x + acc)
        == foldr(xs, 0, fn(x, acc) => x + acc) + foldr(ys, 0, fn(x, acc) => x + acc);
    proof by use fold_append(xs, ys, fn(x) => x, 0, fn(a, b) => a + b);
}
law count_append(xs: List<Bool>, ys: List<Bool>) {
    foldr(xs.concat(ys), 0, fn(x, acc) => choose(x, 1, 0) + acc)
        == foldr(xs, 0, fn(x, acc) => choose(x, 1, 0) + acc) + foldr(ys, 0, fn(x, acc) => choose(x, 1, 0) + acc);
    proof by use fold_append(xs, ys, fn(x) => choose(x, 1, 0), 0, fn(a, b) => a + b);
}

// ------------------------------------------------- Option and Result ----

law option_map_identity<A>(o: Option<A>) {
    o.map(fn(x) => x) == o;
    proof by cases o { none => normalize; some(v) => normalize; };
}
law option_map_fusion<A, B, C>(o: Option<A>, f: fn(A) -> B, g: fn(B) -> C) {
    o.map(f).map(g) == o.map(fn(x) => g(f(x)));
    proof by cases o { none => normalize; some(v) => normalize; };
}
law option_ok_or_map<A, B, E>(o: Option<A>, f: fn(A) -> B, e: E) {
    o.map(f).ok_or(e) == o.ok_or(e).map(f);
    proof by cases o { none => normalize; some(v) => normalize; };
}
law result_map_fusion<A, B, C, E>(r: Result<A, E>, f: fn(A) -> B, g: fn(B) -> C) {
    r.map(f).map(g) == r.map(fn(x) => g(f(x)));
    proof by cases r { ok(v) => normalize; err(e) => normalize; };
}
law result_maps_commute<A, B, E, F>(r: Result<A, E>, f: fn(A) -> B, g: fn(E) -> F) {
    r.map(f).map_err(g) == r.map_err(g).map(f);
    proof by cases r { ok(v) => normalize; err(e) => normalize; };
}

// ------------------------------------------------- maps and buffers ----

law map_set_get<V>(m: Map<u32, V>, k: u32, v: V, d: V) {
    m.set(k, v).get_or(k, d) == v;
}
law map_set_get_other<V>(m: Map<u32, V>, k: u32, j: u32, v: V, d: V) {
    requires distinct: (j == k) == false;
    m.set(k, v).get_or(j, d) == m.get_or(j, d);
}
law map_set_contains<V>(m: Map<u64, V>, k: u64, v: V) {
    m.set(k, v).contains(k) == true;
}
law map_remove_get<V>(m: Map<u32, V>, k: u32, d: V) {
    m.remove(k).get_or(k, d) == d;
}
law buffer_freeze_push<T>(b: Buffer<T>, x: T) {
    b.push(x).freeze() == b.freeze().concat([x]);
}

// ------------------------------------------------ records and vectors ----

law point_x(a: u32, b: u32) {
    Point { x: a, y: b }.x == a;
}
law vector_y(a: f32, b: f32, c: f32) {
    vec3(a, b, c).y == b;
}

// ------------------------------------------- numbers, Bool and choice ----

law int_distributes(a: Int, b: Int, c: Int) {
    a * (b + c) == a * b + a * c;
}
law word_wraps(x: u32) {
    x + 4294967295 + 1 == x;
}
law bool_and_true(p: Bool) {
    (p && true) == p;
    proof by cases p { true => normalize; false => normalize; };
}
law choose_same<T>(c: Bool, x: T) {
    choose(c, x, x) == x;
}
law choose_map<A, B>(c: Bool, x: A, y: A, f: fn(A) -> B) {
    f(choose(c, x, y)) == choose(c, f(x), f(y));
    proof by cases c { true => normalize; false => normalize; };
}
