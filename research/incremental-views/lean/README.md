# Lean versions of the incremental-view laws

These are standalone Lean 4 files with **no imports**: Lean core / `Init` only, no
`set_option`, and no `sorry`. They compile with no errors or warnings under
`lean 4.33.0-rc1` (commit 62eed1db), the nearest release to Hunchroom's
`4.33.0-pre` core build.

```sh
lean IncrementalViews.lean
lean SignedDeltas.lean
```

They restate the Ink entries in ordinary Lean, using `Int` and `List`. Unlike the
first-order Ink kernel, Lean can quantify over the function `f` and the
predicate `p`, so each law below is the *general* form of an Ink schema instance.

## `IncrementalViews.lean`: append (bag-union) semantics

| Lean theorem | Ink entry it generalises | Meaning |
| --- | --- | --- |
| `sum_append` | `sum_append` (exact-integers) | `sum(xs++ys) = sum ys + sum xs` |
| `sum_append_commutes` | `sum_append_commutes` | the total does not depend on the order rows are appended |
| `count_append` | `count_append` | |
| `map_append_linear`, `filter_append_linear` | `map_double_integer_append`, `filter_is_positive_append` | map and filter are linear for **every** `f` and `p` |
| `sum_map_append`, `count_filter_append` | `sum_map_double_integer_append`, `count_filter_is_positive_append` | maintain `sum∘map` and `count∘filter` from the appended rows alone |
| `addition_interchange` | `addition_interchange` | |
| `decompose_filter_map`, `decompose_map_filter`, `decompose_count_filter` | the view-decomposition obligation checked by `ink verify-view` | a pipeline equals the sum of per-row contributions (`if p r then f r else 0`) |
| `join_matches_append`, `join_left_append`, `join_right_append`, `join_delta` | same names | bilinearity of the weighted equi-join aggregate, and its append-expansion |

`joinSum` mirrors the Ink entry exactly. Each pair of rows with equal `UInt64`
keys contributes `value_a + value_b`, and each row's matches are folded tail
first, as `join_matches` and `join_sum` are.

## `SignedDeltas.lean`: signed multiplicities, kept separate

A delta is a list of `(element, weight)` pairs. A negative weight is a
retraction. `total f` is the weighted sum `Σ w · f x`.

| Lean theorem | Meaning |
| --- | --- |
| `total_append` | totals are additive over concatenated deltas |
| `total_negate` | negating every weight negates the total |
| `retraction_cancels` | a delta followed by its negation contributes nothing |
| `signed_replacement` | replacing `old` with `new` is `−1·old + 1·new` |
| `total_insert_anywhere` | the position of an inserted weighted element is unobservable in the total |

## What these laws do *not* say

- **Append versus unique-key tables.** The append laws describe bag union.
  Stored Ink tables have unique keys, so an insert/replace/remove is a table
  transition, not an append. The exact-maintenance `sum_insert`/`sum_replace`/
  `sum_remove` entries cover those transitions, and the source-row bridge binds
  them to the actual table.
- **Negative deltas.** These appear only in `SignedDeltas.lean`, as explicit weights.
  Payload negation is not retraction: `-3 + 4 = 1`, whereas retracting a row of
  value `3` from a total of `7` leaves `4`.
- **Observable iteration order.** The order-independence results are about
  *totals*. They make no claim about the order of an output list, about event
  order, or about any query that exposes enumeration order.
