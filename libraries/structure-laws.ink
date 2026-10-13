module ink.knowledge.structure_laws;
// Laws stated once over algebraic structure, never over a carrier type or a
// named operator. Each fold step is a single function parameter, so a program
// site binds it by ordinary matching; every assumption is proved again for the
// concrete step at each use (see ink_knowledge/structure_instances.py). These
// declarations grant no applicability or profitability authority.

// ------------------------------------------------ absorbing accumulators ----
// Once a left fold's accumulator is absorbed, no later item changes it.
law absorbed_stays<A, S>(xs: List<A>, s: S, op: fn(A, S) -> S, absorbed: fn(S) -> Bool) {
    requires absorbed(s);
    assume absorbs(x: A, t: S) requires absorbed(t): op(x, t) == t;
    foldl(xs, s, op) == s;
    proof by induction xs {
        nil => normalize;
        cons(h, tail) => calc {
            _ == foldl(tail, op(h, s), op) by normalize;
              == foldl(tail, s, op) by congruence(normalize, assumption absorbs(h, s) requires (hypothesis 0), normalize);
              == _ by ih;
        };
    };
}

// Early exit for any accumulator with an absorbing state: Boolean and/or with
// false/true, products with zero, saturating minima and maxima, and so on.
law absorbing_foldl<A, S>(xs: List<A>, z: S, op: fn(A, S) -> S, absorbed: fn(S) -> Bool) {
    assume absorbs(x: A, t: S) requires absorbed(t): op(x, t) == t;
    foldl(xs, z, op) == fold_until(xs, z, fn(x, t) => absorbed(t), op);
    proof by induction xs generalizing (z) {
        nil => normalize;
        cons(h, tail) => cases absorbed(z) {
            true => calc {
                _ == foldl(tail, op(h, z), op) by normalize;
                  == foldl(tail, z, op) by congruence(normalize, assumption absorbs(h, z) requires (hypothesis 0), normalize);
                  == z by use absorbed_stays(tail, z, op, absorbed) requires (hypothesis 0)
                         assuming (assumption absorbs(__assumed_x, __assumed_t) requires (hypothesis 1));
                  == op(h, z) by symmetry(assumption absorbs(h, z) requires (hypothesis 0));
                  == _ by normalize;
            };
            false => calc {
                _ == foldl(tail, op(h, z), op) by normalize;
                  == fold_until(tail, op(h, z), fn(x, t) => absorbed(t), op) by ih(z = op(h, z));
                  == _ by normalize;
            };
        };
    };
}
