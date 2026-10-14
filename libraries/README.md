# Ordinary Ink libraries

These are baseline source definitions, linked before bounded generic elaboration.
They confer no optimisation authority. Alternative algorithms need canonical
entries and checked correspondence/equivalence evidence; measurements rank only
admitted alternatives.

`collections.ink` defines an abstract refined Set interface with structural
identity, stable construction and invariant-preserving union, intersection and
difference. Callers use `elements`, `has` and `size`; raw boundaries validate the
invariant. The generic list implementation remains a quadratic baseline.
`producers.set_contracts` authors ordinary source-bound preservation proofs from
shared fold laws with finite search budgets. The library also provides callback
traversal/reduction, first-appearance grouping and duplicate-preserving left-major
equijoins.
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

`storage-regions.ink` and `chunked-sequences.ink` are abstract generic storage
interfaces implemented with ordinary owned buffers and nested finite loops.
The arena stores variable-size rows in one payload sequence with checked relative
spans. Chunk construction retains complete and final partial chunks. Successful
values carry range/width invariants; raw ingress still validates them. Handles
are relative coordinates without allocation provenance. Result-validity evidence
is ordinary canonical contract laws; universal codec round trips, broader refined element/owner proofs, direct borrowed views and profitability measurements remain work in
progress. See the distribution's `docs/storage-regions-foundation.md`.


`storage-observations.ink` proves a general observation law for left folds with a
checked per-step assumption, plus list and owned-buffer instances. Its theorem
is reusable across element/state types; an instance must establish its own step
relation. These are ordinary canonical laws and do not establish an arena or
chunked-sequence codec relation merely by naming that representation.

`owned-values.ink` exercises generic Buffer-backed refined-element copying.
`local-relations.ink` supplies checked frame, simulation and conditional relation
laws for ordered folds. `buffer-views.ink` uses scoped read-only clipped ranges;
`buffer-view-laws.ink` checks their logical slice observations. Algorithms remain
source, and every use of a law still proves its assumptions.

`checked-trees.ink` supplies an abstract recursive tree whose every nested payload
retains the checked unique-value interface. Construction, observations and
immutable replacements have portable recursive definition contexts and 72
independently replayed pure obligations in the imported conformance fixture.

`recursive-trees.ink` supplies a generic finite tree with ordered leaf traversal,
leaf counting and mirroring. Source admission checks proper immutable subvalue
descent; execution does not confer an induction or representation certificate.
`producers/termination_measures.py` separately proposes source-bound unsigned and
lexicographic decreasing-measure certificates, replayed by the core RUP checker.

The incremental library retains the both-input join cross term and exact signed
deletion cancellation. These algebraic laws alone do not admit an executable
maintained representation or establish profitability.

`math.ink` defines exact float min/max/clamp/absolute value and scaled vector
length/normalisation, plus explicitly bounded `*_approx` trigonometry, exponentials
and logarithms. The algorithms are ordinary ordered F32 source. `text.ink` defines
chunked text construction, flattening, fallible UTF-8 byte lengths, slicing, search
and insertion. Their new fixed operations bind executable core V11.

`producers.numeric_text_laws` supplies 39 checked choice-distribution instances for
individual arguments of numeric, word and UTF-8 primitives. They do not authorise
float reassociation or replacing division by reciprocal multiplication.

`sequence-filter-laws.ink` proves that folding a filtered sequence equals folding
the original sequence with a conditional step. Set preservation uses it with
general fold simulation and prefix observation; it adds no compiler Set case.

`producers.contract_proofs --source-evidence` replays supplied pure and state
certificates against fresh source-derived goals. It retains their exact proof
trees and searches only for missing obligations; hashes and old verdicts never
replace replay.
