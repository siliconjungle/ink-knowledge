# Incremental-view laws (DBSP-style)

This library holds the algebra that makes incremental view maintenance
compositional. It reuses the 35 exact-integer objects unchanged, and adds 20
definitions and theorems. All of them are checked by the unchanged generic kernel
(`ink verify-library incremental-views/lock.json`). The kernel has no new
primitive, axiom or rule for them.

| Law | Statement (`++` is append, `+` exact integer addition) | Why it matters |
| --- | --- | --- |
| `map_double_integer_append` | `map_f(xs ++ ys) = map_f(xs) ++ map_f(ys)` | map is linear, so its delta is the map of the delta |
| `filter_is_positive_append` | `filter_p(xs ++ ys) = filter_p(xs) ++ filter_p(ys)` | filter is linear (proved with Boolean case analysis) |
| `sum_map_double_integer_append` | `sum(map_f(xs ++ ys)) = sum(map_f ys) + sum(map_f xs)` | maintain `sum ∘ map` by adding the delta's contribution |
| `count_append`, `count_filter_is_positive_append` | `count(filter_p(xs ++ ys)) = count(filter_p ys) + count(filter_p xs)` | maintained filtered counts |
| `sum_append_commutes` | `sum(xs ++ ys) = sum(ys ++ xs)` | order independence, which licenses hash or any-order layouts for the aggregate |
| `addition_interchange` | `(a+b)+(c+d) = (a+c)+(b+d)` | rearrangement used by the join proofs |
| `join_left_append` | `join(as ++ da, bs) = join(da, bs) + join(as, bs)` | the join aggregate is linear in its left input |
| `join_right_append` | `join(as, bs ++ db) = join(as, db) + join(as, bs)` | it is also linear in its right input, so it is bilinear |
| `join_delta` | `join(as ++ da, bs ++ db) = (join(da,db) + join(da,bs)) + (join(as,db) + join(as,bs))` | the append-expansion identity, a foundation for insertion-only join maintenance |

How these are defined:

- **join:** `join_sum(as, bs)` is the sum, over every pair with equal `U64`
  keys, of `value_a + value_b`. Pairs with different keys contribute 0. Rows are
  `KeyedRows` (key, exact-integer value).
- **Order independence of insertion:** the existing `sum_insert` /
  `sum_row_decomposition` laws already cover inserting at any position.

## Schemas, not one-off facts

The kernel is first-order, so each law is proved for one concrete function or
predicate: `double_integer`, `is_positive`, and the join's `value_a + value_b`.
In `tools/incremental_view_proofs.py`, `linear_map(name, f)` and
`linear_filter(name, p)` generate the same proof for *any* scalar function or
predicate, because the induction never inspects the function's body. A search
tool can instantiate them for an actual program's lambdas, and the kernel checks
every instance again.

## Validation

- `ink verify-library incremental-views/lock.json` reports `verified` (55-object
  closure).
- `python3 tools/catalogue.py verify` covers all 35 indexed packages, including
  this one.
- **Negative control:** a copy whose `join_right_append` claims
  `join(as, bs ++ db) = join(as, bs)` is rejected with "inductive proof proves a
  different statement".

## Append scope and signed deletions

These join laws are additive over list append. They do not establish signed
multiset deletion, replacement or the full DBSP group interpretation. Here the
value is an application payload, not a signed multiplicity: negating it does
not negate a joined pair. For example, joining `(k,3)` with `(k,4)` contributes
7; joining `(k,-3)` with `(k,4)` contributes 1, so the latter does not cancel
the former. A signed-delta model must represent multiplicity separately and
prove its cancellation and update correspondence.

Sum order-independence applies to the aggregate observation. It does not by
itself authorise changing the order of a program's observable row enumeration,
events or snapshots. Map/filter template instantiation is producer machinery;
these concrete entries do not automatically bind arbitrary source lambdas.

## Scope

This is mathematics only. It does not authorise any source or stateful
transformation. To use a law, a correspondence check must bind these definitions
to the program's actual table, projection and update, as
`exact-maintenance` does for sums. The transactional protocol (abort,
tentative reads, ordered events) also has to be covered; see
`docs/transaction-plans.md` in ink-lang.
