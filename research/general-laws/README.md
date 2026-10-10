# General collection laws

Eight laws about lists, stated once over abstract symbols and checked once by
the first-order kernel. A concrete program reaches them only through the
kernel's `Instance` rule; nothing here is usable as a closed fact.

Produced by `producers/general_laws.py` (untrusted). Every object is checked
individually with `ink verify-library` while it is written, and the lock is
checked as a whole at the end.

## Abstract symbols

| Kind | Entries |
| --- | --- |
| sorts | `Element`, `Image`, `Source`, `Total` |
| functions | `plus(Total, Total)`, `zero()`, `map_function: Element → Image`, `inner_map_function: Source → Element`, `predicate`, `inner_predicate: Element → Bool`, `image_weight: Image → Total`, `weight`, `other_weight: Element → Total` |
| assumptions | `zero_right: plus(a, zero()) = a`, `zero_left: plus(zero(), a) = a`, `plus_associates`, `plus_commutes`, `weights_agree: weight(head) = other_weight(head)` |

The derived definitions are ordinary lists and folds over those symbols:
`ElementList`, `ImageList`, `SourceList`, `map`, `filter`, `sum`, `append`,
and so on. They use the compiler's binder names (`xs`, `head`, `tail`), so the
compiler's exported view stages are literal instances of them.

## Laws

| Law | Statement | Rests on |
| --- | --- | --- |
| `sum_map` | `sum_g(map_f(xs)) = sum_{g∘f}(xs)` | — |
| `sum_filter` | `sum_w(filter_p(xs)) = sum_{p ? w : 0}(xs)` | `zero_right` |
| `sum_congruence` | `sum_w(xs) = sum_v(xs)` | `weights_agree` |
| `sum_append` | `sum_w(xs ++ ys) = sum_w(xs) + sum_w(ys)` | `zero_left`, `plus_associates`, `plus_commutes` |
| `map_append` | `map_f(xs ++ ys) = map_f(xs) ++ map_f(ys)` | — |
| `filter_append` | `filter_p(xs ++ ys) = filter_p(xs) ++ filter_p(ys)` | — |
| `map_fusion` | `map_f(map_e(xs)) = map_{f∘e}(xs)` | — |
| `filter_fusion` | `filter_p(filter_q(xs)) = filter_{q && p}(xs)` | — |

`count` is `sum` with a constant weight, so the sum laws cover it.

## Using a law

`Proof::Instance` takes:

- a sort for each abstract sort,
- a closed term (a `Lambda`) for each abstract function,
- an existing definition for each derived datatype or function the statement
  reaches. The kernel checks that the definition's declaration is exactly the
  instantiated general one, up to binder names.
- a checked proof of each assumption the law depends on, for that
  interpretation.

It must interpret exactly the law's abstract parameters. A theorem that uses an
abstract symbol or an assumption without instantiating it stays parametric, and
`Context::check` refuses parametric conclusions. In particular, an assumption
cannot leak into a program obligation.

The compiler's `--prove-views` producer (`producers/view_decomposition.py`)
builds every maintained-view proof from `sum_map`, `sum_filter` and
`sum_congruence`. It does no per-program induction. For exact integers both
assumptions are discharged by computation.

## Non-claims

- These are mathematical laws about logical lists. Binding them to a program
  still relies on the compiler's source-to-logic translation and on the
  native/runtime correspondence; both remain separate trust boundaries.
- `sum_append` needs a commutative monoid. The integer instance is not used by
  the view producer today.
- Signed multiplicities, retraction and joins are not here yet. The Lean files
  in `incremental-views/lean` state them, and the specialised first-order joins
  live in `incremental-views`.
