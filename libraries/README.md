# Ordinary Ink libraries

These are baseline source definitions, linked before bounded generic elaboration.
They confer no optimisation authority. Alternative algorithms need canonical
entries and checked correspondence/equivalence evidence; measurements rank only
admitted alternatives.

`collections.ink` defines stable list-based sets, callback traversal/reduction,
first-appearance grouping and duplicate-preserving left-major equijoins.
`integers.ink` defines checked word division/remainder with separate zero-divisor
and signed-overflow errors. See the distribution's generic-language-foundations
contract for syntax, ordering, wire shapes and limitations. Generic templates are
checked when instantiated. These libraries require that foundation's core and
backend revisions.

The set and join algorithms deliberately expose a baseline for comparison; no
speedup claim is established by their presence in this repository. The external
finite-list producer separately supplies locally checked work-skipping laws.

`value-laws.ink` is external theorem authoring source. Use `ink emit-laws` or
`producers/source_laws.py`; application compilation rejects its rewrite declarations.
Exact-integer laws use the general bounded ring checker, with no trusted labels.

`general-laws.ink` and `incremental-laws.ink` are external law sources in Ink's
one `law` form: type parameters, function parameters, conditions, quantified
assumptions and proofs (see the distribution's `docs/laws-in-source.md`).
`general-laws.ink` covers lists, folds over any monoid, Option/Result, maps,
buffers, records, vectors, `Int`, words and Bool; `incremental-laws.ink` states
the delta rules of sum, group-by, join and views over views over signed
collections. General laws reach programs only through concrete instances that
prove their assumptions. Both libraries export to Lean with `ink-to-lean`.
