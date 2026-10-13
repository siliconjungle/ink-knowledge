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

`invariant-values.ink` defines abstract unique collections, sorted words, bounded
indices and indices tied to an immutable sequence. Construction and operations
carry ordinary checked predicates; callers use the public observers. It requires
the distribution's value-invariant and abstract-record source machinery. Source
opacity does not remove public input validation or establish faster execution.

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

`buffers.ink`, `voxels.ink`, `codecs.ink` and `ecs.ink` exercise the V9 general
owned range machinery. They supply stable column movement, dense voxel box
painting, bounded word-stream run-length decoding, packed octet serialisation,
and sparse component gathering. They add no compiler algorithm recognisers.
The external bulk-buffer producer separately publishes checked range identities
and fill length invariants. See the distribution's `docs/bulk-buffer-workloads.md`
for admission, CPU/device boundaries, reproducible measurements and limitations.

`json.ink` defines the ordinary recursive `Json` datatype and object algorithms:
constructors, typed accessors, missing-versus-null lookup, replacement, removal
and projection. Number tokens preserve exact spelling; member order is observable.
The ABI's checked text boundary rejects duplicate names and invalid number tokens.
Source constructors can create malformed JSON documents, so conversion back to
JSON is explicitly fallible. No compiler JSON algorithm recogniser is added.

`json-laws.ink` supplies generic lookup-after-replacement, empty lookup,
projection idempotence and projection/map fusion, plus searchable String
instances. `producers/json_laws.py` publishes six ordinary checked laws and their
dependencies into the active snapshot and `json-view.json`. Conditional premises
must be proved at use sites. These laws concern source list/value semantics;
the operational Rust/JavaScript binary codecs remain trusted and tested.
