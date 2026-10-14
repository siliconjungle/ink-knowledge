# Ink knowledge

Immutable knowledge data for [Ink](https://github.com/siliconjungle/ink-lang), with a rebuildable SQLite discovery index. Search and execution policy live in [ink-planner](https://github.com/siliconjungle/ink-planner); proof checking stays in Ink's independently buildable semantic core. Storage never grants proof authority.

## Storage contract

`ink_knowledge/automatic-selection.json` owns bounded pure-call probe sizes,
distributions, measurement controls and the required profitability margin.
`selection_probes.create(core)` authors probes from supported exact typed
signatures and source constants; it does not use function names or theorem IDs
to choose behaviour. Recursive/unsupported transfers and state/action/event
lifecycles decline. Synthetic probes are workload proposals, not observed user
usage or correctness evidence. Planner measurement and proof checking remain
separate. `ProposalViews.update` refreshes authenticated proposal membership for
intermediate search states; membership still grants no theorem authority.

`store/objects/<sha256>.json` contains canonical entries. Every entry has exactly these fields:

```json
{
  "schema": 1,
  "kind": "rewrite",
  "semantics": "ink-conditional-laws-v1",
  "dependencies": [],
  "interface": {
    "parameters": {},
    "result": null,
    "operations": [],
    "effects": [],
    "conditions": []
  },
  "payload": {}
}
```

Kinds are `definition`, `theorem`, `rewrite`, `implementation`, `representation`, `maintenance`, and `bridge`. The semantics version determines the typed payload and admission domain. Declaring a kind or storing a proof does not implement its checker: unsupported domains reject. Mathematical definitions, scalar theorems, inductive theorems and executable semantic laws use this common entry contract. Program-specific certificates still have specialised proof terms; they are not automatically admitted as executable laws.

Identity is SHA-256 of UTF-8 JSON with lexically sorted object keys, no whitespace, and no trailing newline. Files add one newline for readability. JSON numbers are integers in the shared Rust/Python range; measured durations are decimal strings. Dependencies and index lists are sorted and unique. Display names live separately and have no authority. The Rust checker verifies the typed mathematical interface against the payload.

`store/trees/` contains authenticated sorted leaves of at most 64 IDs and binary branch nodes. `store/snapshots/<id>.json` pins a Merkle root; `store/snapshot.json` selects the current snapshot. A bounded exported view carries selected roots, their exact dependency closure and membership proofs. The core authenticates membership, hashes, semantics, proof terms and applicability. It never needs the complete database. New snapshots do not invalidate replay of a plan carrying an older pinned view.

`store/observations/<id>.json` stores performance evidence separately. Each observation pins program, plan and knowledge IDs; hardware, driver, toolchain, backend and bridge; shape, distribution, concurrency and residency; full-call nanosecond samples and peak allocation (`null` when unmeasured, distinct from measured zero). Observations do not change the proof snapshot or become proof premises.

Formal storage schemas are in `schemas/`. Canonicalization, sortedness, hashes, exact dependency closure and mathematical validity require the library/checker in addition to JSON Schema validation.

## Query API

Install with `python3 -m pip install -e .`, or use `PYTHONPATH=.` in a source checkout. Python 3.10+ and SQLite 3.37+ are required.

```python
from ink_knowledge import Store
store = Store('/path/to/ink-knowledge', '/path/to/pinned-snapshot.json')
store.rebuild()
ids = store.query(kind='rewrite', semantics='ink-conditional-laws-v1',
                  operation='binary:+', result={'Value': 'U32'}, limit=128)
view = store.bundle(ids)
```

Queries also support parameter types, effects, exact applicability conditions and an `after` ID for paging. `ink_knowledge/index.sql` specifies the SQLite schema with explicit tables for snapshots, entries, membership witnesses, dependencies, types, operations, effects, applicability, names and observations. Result order is deterministic. Indexed subset export loads only its selected objects and dependency closure, authenticating cached membership witnesses against the pinned root.

`store.bundle(roots)` uses one SQLite connection and read transaction for the
selected dependency closure. Identical membership proof bytes share Merkle-path
authentication within that export, while every ID must occur in its authenticated
leaf. Each object is independently read, validated and hashed. Witnesses are
retained for the output rather than fetched a second time. Indexed authentication reuse
ends with the call; later exports recheck indexed proofs and canonical content.
No full-tree scan is needed when exporting an indexed subset. The index-free
path, exact bundle format and depth/1024-object limits are unchanged.

`store.observations(program, plans, target, workload, limit=1024)` filters the
requested plans in SQL before applying the result limit. It reads and hash-validates
only matching canonical evidence files. Up to 1024 distinct plans are accepted;
an empty plan set or zero limit needs no index or file access. Rebuild existing
indexes to gain the covering observation index; older indexes remain compatible
with the corrected query. Exact target/workload matching and canonical validation
still determine comparability. Index tampering cannot create admissible evidence.

```sh
python3 -m ink_knowledge --root . rebuild
python3 -m ink_knowledge --root . query --kind rewrite --operation binary:+
python3 -m ink_knowledge --root . export --entries ENTRY_SHA256 -o view.json
/path/to/ink knowledge-check program.core.json view.json
python3 -m unittest discover -s tests -v
```

`index.sqlite` is ignored and disposable. Rebuilding atomically replaces it from canonical Git objects; a cache from another snapshot is rejected. A future database service must retain this object/snapshot/view contract. The database is an untrusted supplier of proof data, not an authority. Explicit snapshot pins can authenticate and query their canonical trees when the active SQLite index belongs to another snapshot; this never changes the active index or chooses a newer catalogue. Active-pointer queries retain their explicit stale-index error.

## Authoring and research

`producers/` holds untrusted authoring/import tools. `research/` quarantines historical experiment formats, fixtures and Lean work; production discovery does not scan it or depend on experiment directory names. Research tools can still reproduce their original mathematical experiments. These formats are not compatibility aliases for the canonical API.

The earlier merged snapshot contained 2845 canonical entries and 4517 discovery names.
It combines the independently developed main catalogue with the web
performance catalogue and the owned-collection/point-query additions, preserving both sets of immutable proofs, observations
and historical snapshots. SQLite remains a rebuilt disposable index. Frozen web
benchmark timings describe their recorded compiler and catalogue revisions; they
do not measure this merged engine.

The initial snapshot contained 648 canonical entries, including 89 executable semantic laws. Earlier snapshots are retained; 20 checked append-view entries and six fixed change-boundary definitions/theorems were added without changing the existing rewrite payloads. The change-boundary laws bind to shared language primitives, but do not certify action bodies or physical rollback. See `research/incremental-views/canonical-review.json` for proof-admission evidence and scope. Reproduce its data with `python3 producers/build_store.py --output /tmp/ink-store`; this explicitly imports the research fixtures as an authoring operation. `store/rewrite-view.json` is a transport fixture for integration tests, not a second storage format or discovery API.


The web performance contribution adds 47 wrapping-word and pure collection laws
without changing the checker: repeat subtraction/product/identity/cancellation,
scaled/zero sums, discarded maps before counts, constant and redundant filters,
and filter composition. F32 laws only rearrange pure collection traversal, not
floating-point arithmetic. [Reproduction and proof evidence](research/performance-laws/README.md)
include 47 accepted objects, eleven selected/replayed U32 applications and two
hash-valid semantic rejection controls. Timings belong to separate web benchmark
reports; proof admission alone makes no speed claim.

To extend a reproduced initial store, build Ink and run:

```sh
python3 producers/publish_performance_laws.py --root /path/to/ink-knowledge \
  --compiler /path/to/ink --report /path/to/publication.json
```

This stages the complete extension, checks the new proof view with Ink, then
publishes a canonical snapshot and rebuilds discovery. It retains previous
snapshot replay and records the unchanged compiler identity.
The independently developed main catalogue reached 1101 canonical entries, including 295 checked semantic laws and source-bound representation/cache-maintenance candidates (`research/cache-maintenance`, `research/compact-queries` and state-reusing bridges in `research/layout-switch`). Earlier snapshots are retained; 20 checked append-view entries, six fixed change-boundary definitions/theorems and 46 general-law entries (`research/general-laws`: abstract sorts, functions and assumptions with eight parametric collection laws) were added without changing the existing rewrite payloads or name targets. The change-boundary laws bind to shared language primitives, but do not certify action bodies or physical rollback. See `research/incremental-views/canonical-review.json` for proof-admission evidence and scope. Reproduce its data with `python3 producers/build_store.py --output /tmp/ink-store`; this explicitly imports the research fixtures as an authoring operation. `store/rewrite-view.json` is a transport fixture for integration tests, not a second storage format or discovery API.

Eleven effect-prefix composition entries add outer path/value/exit definitions,
sequencing and six checked laws. Their definitions bind to the core's fixed
finite composition operation. They are not a source-analysis soundness theorem,
whole-action refinement or authority to skip rollback. See
`research/effect-composition/README.md`. The 42 executable rewrite entries remain
unchanged.

Four stable `research/action-laws` entries add parametric table-removal idempotence. The whole-action producer interprets this one law for each actual row sort; it does not regenerate a per-program induction proof. Source transition definitions and evidence are individual database objects, transported in a pinned view. See `research/action-laws/canonical-review.json`.


The local-collection pass adds 45 executable semantic laws: buffer freeze/read
observations, successive filter fusion, identity filtering, zero-bound iteration,
immediate stopping and stopping proved by an actual application condition. Each
family covers u32/u64/i32/f32/Bool values. `producers/local_collection_laws.py`
reproduces the entries and the bounded `store/local-collection-view.json`; the
`build_store.py` reproduces its base authoring snapshot; later producers preserve
and extend the checked-in snapshot. These require Ink's
buffer-observation/stopping-loop correspondence (core commit 77a47a6), and are
checked locally. They do not prove owned mutation, map updates, heap correctness,
A* correctness, physical emission or a universal speedup.

The collection-pipeline extension adds 80 checked laws with no core change:
length after map (25 input/output type combinations), map/fold and filter/fold
fusion for sum/difference/product (four numeric types each), combined filter/map/fold fusion
(twelve laws), and integer sum fusion (nine laws), and zero length/count after an always-false
filter (five types each). `producers/collection_pipeline_laws.py` and
`store/collection-pipeline-view.json` reproduce them. Fold fusion preserves
right-fold operation order and initial value; it introduces no associativity or
floating arithmetic law. The existing same-sort numeric foldr interface bounds
the supported fold families. Previous canonical objects and snapshots remain.

The shared-sequence extension adds 83 checked laws: count after mapping (25),
same-sequence zip projections (10), and raw/left-mapped/right-mapped/both-mapped
zip fusion with ordered sum/difference/product (48). All use ordinary list
induction with the unchanged compiler and checker. Zip fusion requires the
exact same source sequence in both branches; no independent-list equality,
length truncation assumption, commutativity or floating arithmetic law is used.
`producers/shared_sequence_laws.py` and `store/shared-sequence-view.json`
reproduce the new entries.

The sort aggregation extension adds nine executable roots and nine checked
insertion dependencies for u32/u64/i32 length, count and sum after sorting.
Ordinary list induction, comparison cases and exact lemma instantiation remove
sorting when only its aggregate is observed. Integer sum uses wrapping
arithmetic; no floating sum or arbitrary reducer law is added.
`producers/sort_cardinality_laws.py` and `store/sort-cardinality-view.json`
reproduce these entries. The full rewrite view carries 259 roots and the nine
insertion dependencies; canonical bytes remain the storage authority.

The filtered-sort extension adds nine executable aggregate laws and eighteen
conditional insertion lemmas. It removes sorting before a value-based filter
when only length/count/wrapping integer sum is observed, for u32/u64/i32.
Kept/dropped insertion conditions are discharged in the sort proof; no predicate
premise is demanded of source callers. Observed ordered outputs retain sorting.
`producers/filtered_sort_laws.py` and `store/filtered-sort-view.json` reproduce
them. The full rewrite view now carries 268 executable roots and 27 proof-only
insertion dependencies. No compiler, core, planner or backend change is needed.

The batch33 independent-list scan projection extension removes a scan whose values are unused by a zip callback, preserving the shorter-list extent. Six U32/I32/U64 endpoint laws, twelve supports, four source-bound certificates and four shared Normalize transports add 26 checked objects (22 fresh, four shared old transports). `producers/web_pipeline33_laws.py`, `producers/publish_web_pipeline33.py` and `tests/test_web_pipeline33_laws.py` reproduce and admit the extension. The canonical catalogue now has 2,485 entries. The 840 separately recorded empirical benchmark groups bring observations to 22,580; they are performance evidence, not mathematical certificates. No production compiler or runtime changes are required.

Batch34 adds six U32/I32/U64 unused-map projection endpoints derived from existing map identity and independent mapped-zip/postmap fusion, plus four content-bound source certificates. Zip retains the shorter-list extent and composed helpers retain their exact definitions. These direct DB endpoints improve bounded search without a new core rule. `producers/web_pipeline34_laws.py` and `tests/test_web_pipeline34_laws.py` reproduce them; tests pin the original catalogue for later replay. The general `producers/publish_web_pipeline33.py` utility admits and publishes the closed extension. Canonical totals are now 2,495 entries and 23,420 separate empirical observations.

Batch35 adds nine U32/I32/U64 direct observed mapped-zip fusion endpoints (left, right and both mapped), derived from map identity and existing batch17 mapped-zip/postmap fusion, plus four content-bound source certificates. Both paired values, mapper order and the shorter-list result extent are preserved. The direct endpoints expose existing algebra to ordinary bounded search, with no new core rule. `producers/web_pipeline35_laws.py` and `tests/test_web_pipeline35_laws.py` reproduce them using the original catalogue pin. The existing general publisher admits the closed extension. Canonical totals are 2,508 entries and 24,260 separate empirical observations. Measured profitability is mixed and distinct from correctness; observations retain regressions and do not install a runtime or cost-model policy.

Batch36 adds four content-bound U32 source deployment certificates for plain, nested, filtered and concatenated ordered folds through named helpers. Existing arbitrary map/fold, filter/map/fold and concat/fold laws supply the mathematics; no new generic law is duplicated. Exact reachable direct/transitive helper definitions are bound by content hash, preserving all inputs and accumulator order. `producers/web_pipeline36_laws.py` and `tests/test_web_pipeline36_laws.py` pin the original catalogue for reproducible replay. The unchanged publisher admits a seven-object closure (four fresh certificates plus three old U32 dependencies); the full producer also checks old I32/U64 laws. Canonical totals are 2,512 entries, 4,259 discovery names and 25,100 separate empirical observations after adding 840 groups. Gains are measured against the full prior and already-fused controls: GPU profitability is mixed, Rust remains faster overall, and correctness admission does not install a runtime/cost policy. All previous entries, names and observation bytes are preserved.

Batch37 adds six U32/I32/U64 independent-list indexed-map demand-erasure endpoints, twelve Nat-offset/beta induction supports and four helper-bound U32 source certificates. Both zip orientations preserve min-length extent and selected value order while removing arbitrary pure total unobserved indexed callbacks. Generalized supports cover Nat index state and wrapping U32 callback indices. `producers/web_pipeline37_laws.py` and `tests/test_web_pipeline37_laws.py` pin the original 2,512-entry snapshot; a full forward/reverse alpha endpoint audit finds no duplicates, without claiming nonderivability from prior laws. The unchanged publisher admits a closed 22-object extension with no old dependencies. Canonical totals become 2,534 entries, 4,281 names and 25,940 separate empirical observations after 840 new groups. Benchmarks consume every vector word; physical GPU dispatch/transfer contracts remain unchanged, five prior cells regress and all strong controls are retained. Correctness and measured profitability remain separate; no runtime/cost policy is installed.

Batch38 adds six U32/I32/U64 same-origin padded observed indexed-zip fusion endpoints, six Nat-beta supports and four content-bound U32 source certificates. Both indexed mapper values and the ordered pair helper remain observed; output extent is length(xs), and arbitrary padding must be appended after the exact shared input prefix. The induction generalizes over arbitrary Nat offsets with wrapping U32 callback indices. `producers/web_pipeline38_laws.py` and `tests/test_web_pipeline38_laws.py` pin the original 2,534-entry snapshot. A full consistent-alpha forward/reverse endpoint audit finds no duplicates for the twelve new generic objects, without claiming nonderivability from older laws. The unchanged publisher admits sixteen fresh objects, no shared-old objects or old mathematical dependencies. Canonical totals become 2,550 entries, 4,297 names and 26,780 empirical observation files after 840 new groups; old objects, names and observation bytes are preserved. GPU requests execute four graph stages before and one legacy shader after selection, while upload grows by twenty bytes and readback is unchanged. All twenty classified prior CPU regressions, uncertainty and strong controls remain recorded; correctness and measured profitability stay distinct. No core, runtime, target routing or cost policy changes are installed.

## Owned collections and incremental point queries

`producers/owned_collection_laws.py --output-store .` adds 215 ordinary laws
for existing Buffer/Map operations and owned stopping loops, preserving older
canonical objects, name targets and snapshots. `store/owned-collection-view.json`
is a transport fixture. Primitive meaning belongs to the core; these entries are
not trusted merely because this producer generated them.

`producers/point_delta.py` proposes fixed-key remove/replace maintenance through
`representations.py --cache-query zero --preserve-cache --delta-query`; unsupported
updates use refresh. Frozen requests and proved forward/reverse migrations live
in `research/point-delta`. `representation_bridge.py --via-logical` proposes
decode/encode bridges; the default proposes state reuse for identical relations.
Every request and bridge still needs mathematical admission.

`producers/lifecycle_observations.py` imports measured native phases with exact
request-file SHA256 identities and exact bridge-file hashes for migration phases.
Checking cost depends on closure/witness bytes, so a representation entry ID alone
is insufficient for comparable measurements. Observations remain separate from
proof snapshots. The current point-delta fixture loses to the simpler direct
layout; no profitability claim follows from its preservation proofs.


## Independent Boolean proof verdict

`research/verified-kernel/BooleanKernel.lean` proves soundness of a separate
Boolean equality calculus in Lean 4.19.0, without added axioms, `sorry` or
`native_decide`. Its standard axiom dependencies are `propext` and `Quot.sound`.
`producers/boolean_verdict.py` translates a bounded subset of historical Boolean
equality objects into certificates; the translator is not verified. The Ink CLI
`check-boolean-verdict` checks the exact input with its Rust checker and then
runs Lean. This optional additional verdict does not verify the entire Ink checker,
source correspondence or backends and grants no new optimisation authority.
Unsupported proof constructors/domains fail explicitly; existing production
snapshot selection and repository-owned contributions are unchanged.

Universal early-exit choices live in `producers/fold_until_laws.py`. Induction,
case proofs and ordinary universal-law composition establish applicability;
accumulator-dependent replacement trees fail closed. Owned map/indexed-map/scan/filter
choices live in `producers/owned_transform_laws.py` and select explicit buffer
operations understood literally by every target.

Performance models live in `store/cost-models` with immutable observation
provenance. They cannot enter mathematical entry discovery. Planner fits them;
`ink-abi` applies their shared native/browser decision contract. Structural search
prices in `ink_knowledge/structural-costs.json` remain unmeasured hypotheses.
The default estimates unknown list callbacks at 16 iterations, uses known literal
lengths, and counts explicit local bindings once. This lets shared construction
and other loop-invariant work compete within bounded search. It is neither a
measured cardinality nor a profitability guarantee; short or empty workloads
can still favour the baseline under complete-call measurements.

The installed producer catalog includes early-termination specialisation and checked
definition unfolding. `ink-plan` runs these untrusted producers, records their source
hashes, and places proposals in an immutable derived snapshot. The configured
canonical snapshot stays intact. Every selected proposal and definition context is
independently checked against the exact input module.

See the distribution’s `docs/storage-bulk-incremental.md` for the checked chunk/index
and Boolean maintenance producers, bulk collection laws, overlapping proof admission,
optional search-hint cache and incremental discovery index. Optimisation evidence
remains untrusted; source-bound proof replay and measured selection are separate.

## Typed indexed and grouped producers

`producers.generic_indexed` derives indexed root products from checked row
constructors and complete action projections. `generic_aggregates` proves typed
U64/Boolean query decompositions without a field-name whitelist; other queries
keep exact evaluation. `grouped_indexed` supplies shared traversals and ordinary
logical/metadata laws for ordered replace/remove pairs. `type_transport` derives
state-carrier codecs and their round trips. Whole-action proofs preserve replies,
errors, events, versions, rollback and future behavior across multiple tables.
The distribution's `docs/general-indexed-batching.md` states the current source
correspondence limits and gives conformance/selection reproduction.

Proof views allow 4096 objects and 64 MB. The source-representation protocol may
list 512 direct dependencies; other entries retain the 128 dependency bound.
Scalar proof templates in `producers/data/word-ring.json.gz` are ordinary checked
certificates, so cold proposal generation does not require a SAT installation.
Stored names, templates and proposal discovery never grant proof authority.

## Reactive dependency laws

`producers/reactive_dependencies.py` publishes three parametric theorems and their
nineteen-entry closure under `reactive-dependencies/` discovery names. They cover
observation reuse through proved dependency factorisation, downstream reuse after
exact value equality, and active-branch reuse with selector/dependency equality.
All abstract assumptions and site conditions must be discharged by concrete
interpretations. They do not admit an arbitrary observed read trace, implement a
runtime scheduler or automatically select a source replacement. Mathematical
admission and the preserved old/new snapshot IDs are recorded in the distribution's
`docs/evidence/signals-state/reactive-laws.json`.

## Disposable search accelerators and untrusted learning evidence

`ink_knowledge.discovery_accelerator.enable(store)` authenticates the pinned
canonical catalogue before deriving typed token buckets, a Bloom filter and
a bounded piecewise linear integer-position hint. Bloom negatives skip impossible
queries. Learned positions use exact local binary search, verify global neighbours
and fall back to full binary search if a hint is invalid. Query filtering and
paging remain exact, including old immutable pins. Object retrieval and proof
export continue to authenticate canonical bytes. Setup and memory are additional
costs; the ordinary SQLite path remains the default.

`ink_knowledge.search_artifacts` stores immutable observations and fitted models
in `store/search-artifacts`, outside mathematical object kinds and discovery.
Models authenticate referenced observations; their hashes and measurements grant
no rewrite authority. Planner's optional HNSW structural sketch likewise supplies
ordering hints, leaving exact membership, matching and proof replay in place.
The distribution's probabilistic-planner report retains warm index gains, setup
costs, approximate recall and the cases where learned positions lose to C bisect.

## Source contract knowledge

`producers.contract_proofs` derives ordinary pure laws and first-order state
proofs from `ink emit-contract-obligations`, replays each proposal, and publishes
canonical entries plus source-bound `ink-contracts-v1` evidence. Static clauses,
`before`, invariants, finite bag observations and uniqueness are checked source
meanings; producers cannot assign their own interpretation.

`producers.invariant_representations` also proposes action guard simplifications
from the exact exported source invariant and action precondition equations.
Boolean wrapper elimination is an authoring heuristic; only the original
boundary equations enter the proof environment. Each replacement requires
ordinary complete observation and future-state preservation proofs. Public
preconditions and restore invariant checks remain, and nested actions retain
their original intermediate-state behavior. `performance/source-precondition-guards`
publishes a checked example closure; source binding, not its name, makes it
applicable. `--max-queries` retains its CLI name but bounds all changed actions.

The database includes `contracts.zero-map-u64`, `contracts.identity-map-u32` and
`contracts.sorted-identity-u64`, and `contracts.unique-id-check-erasure`: two list-induction laws, a conditional uniqueness law and a conditional sort
law. Their definition contexts contain no exact helper bodies. The
`contract-witnesses` recipe proposes specification witnesses, checks the complete
selected module, and publishes ordinary implementation candidates. Contracts can
permit more than one value; refinement is distinct from equality rewriting.

Use `python -m producers.contract_candidates SOURCE OUTPUT --compiler ink` to
publish examples. This bounded producer is deliberately incomplete; explicit
proofs remain available through the existing kernels. Compiler admission checks
every proof regardless of database membership. Performance measurements are
separate immutable observations, never theorem authority. See the distribution's
`docs/source-contracts.md` and `tools/bench_contracts.py`.

The `contract-laws/` source library publishes six checked collection laws.
The `contracts.state-list.*` entries prove initial uniqueness, guarded replacement,
clearing and postconditions for the distribution’s private-list example. Generated
traversal equivalence and data equality reflexivity are ordinary induction proofs
in those dependency closures. Search may weaken premises to prove a stronger
theorem; it never assumes the resulting theorem without kernel replay.

Planner discovery may use `Store.ensure_index()` to reuse an already indexed
immutable snapshot. `refresh_index()` explicitly synchronises discovery and
observation files, and `rebuild()` repairs the disposable cache. Canonical object
hashes, membership witnesses and local proof checking remain the authority for
exported selections. Typed pattern reachability now batches successor heads over
one read connection per discovery pass.

Typed algorithm templates in `libraries/source-algorithms.json` introduce helper functions and intermediate record types through conservative source admission, then supply ordinary equality proofs for their use. `python -m ink_knowledge.source_algorithms libraries/source-algorithms.json --root .` publishes them. `python -m producers.allocation_laws --root .` publishes exact-integer allocation bounds; capacity formulas are data checked against each source. Both remain subject to normal admission and offline profitability selection.

Generic pipeline templates also cover ordered left/right map folds, left-fold
filter/map pipelines, and two first-replacement implementations. The optional
result implementation composes an absorbing-state lemma and evaluates its
predicate once per row, using existing source operations. These are opaque-carrier
laws, including distinct item, mapped and accumulator types; they make no monoid
assumption or floating-point reassociation.

Template discovery can abstract a free function applied to distinct local
variables. It rejects other local dependencies and emits an ordinary adapter
proof with the exact source endpoint. Template matching remains untrusted: the
kernel replays the universal law, adapter, source context and dependency closure.

## Composable knowledge and indexed growth

Source algorithm templates can import other snapshot-owned algorithms, bind their
types, export helper names and reuse their equality proofs. The ordinary producer
assembles a bounded hygienic dependency closure and the compiler checks every
definition and proof. `python -m producers.composed_algorithms --root .` publishes
the partition/filtered-count composition. It reuses two existing families rather
than copying their implementations and inductions.

Physical recipes now carry bounded structural eligibility selectors and compose
independent packing/memoisation sites through `definitions: "selected"`. Proposal
domains and combinations are data; ownership and storage capability checks remain
in the compiler. Selection still requires comparable profitability evidence.

Disposable SQLite projections index structural template paths and explicit
observation/family attribution. Indexed discovery retains all possible matches
and fetches applicable proof dependencies. `ink_knowledge.family_evidence.page`
checks exact target/workload descriptors and authenticates returned observations;
it does not infer missing attribution or grant rewrite authority.

`python -m ink_knowledge --root . pack` produces optional packed object transport
without removing Git objects. Packed reads retain canonical hashes, authenticated
membership and independent proof replay; corrupt loose files take precedence and
fail validation. The distribution's `docs/composable-knowledge.md` records the
scaling curves, strong runtime controls, physical regressions and remaining limits.

## License

Project code and documentation are [MIT licensed](LICENSE). Third-party dependencies,
vendored projects and research data retain their own licenses and notices.

## Traversal elimination and local discovery reuse

`producers.traversal_templates.templates()` contains six new parametric families:
constant filters, unchanged-accumulator left/right folds and length/count over
concatenation. Their concrete instances use ordinary induction and normalization.
They need no compiler recogniser or new execution primitive.

A discovery invocation reuses its bounded source-site traversal, type-instantiated
proof closures and exact higher-order adapters. Caches are local to that exact
source/definition context, retain dependency-depth limits and never replace kernel
replay. Larger operation-head buckets use necessary structural, literal and
concrete-sort constraints; small buckets match directly. Applied higher-order
holes remain unrestricted. See the distribution's `docs/discovery-reuse.md` for
ablation curves and the cases where index construction adds overhead.

## Maintained source folds

`python3 -m producers.maintained_folds SOURCE --compiler INK -o DIRECTORY`
authors an ordinary compiled-plan packet for factorised U64 source keeps. It
proposes row contributions, group operations and eight independently regenerated
proof obligations per keep: exact source factorisation, identity, associativity,
commutativity, cancellation, insertion, deletion and replacement. Arithmetic
covers all 64 bits, including wrapping. Filtered counts, sums and weighted mapped
contributions compose across independent tables.
Use `--publish KNOWLEDGE_ROOT` to extend an existing canonical snapshot with its
proof definitions and source-bound maintenance candidate. Published candidates
are discovered through the normal catalogue and still replay every obligation.

`--dense-capacity N` adds bounded-prefix storage with exact map fallback for every
out-of-prefix key. The registered recipe offers map and dense alternatives; the
planner ranks them using supplied state lifecycle evidence and held-out histories.
Producer patterns and measurements never grant equality authority. The installed
tactic currently handles U64 keys/groups; unsupported authoring domains decline.
The capability itself admits other valid U64/Bool group proofs with supported
source codecs. Current emission is JavaScript only.

See the distribution's `docs/maintained-folds.md` for trusted runtime/controller
limits, ownership, rollback, restore and subscription contracts.

`producers/tagged_word_codecs.py` publishes bounded 1–12-bit tagged-word equations
with explicit payload/tag premises and independently replayed `shared-v2` RUP
certificates. It requires a compiler supporting the explicit circuit mode. Use
`--compiler /path/to/ink --output /private/candidate/store`; publication does not
select a source or backend representation. `tests/test_tagged_word_codecs.py`
checks all widths, false proposals, statement/mode changes and corrupt hints.

`producers.sum_flatten` authors ordinary bidirectional case/conversion proofs for
source-derived right-associated sum codecs. The `private-sum-spines` recipe
proposes individual and combined JavaScript layouts, preserving existing physical
choices. It has no JSON matcher and leaves recursive leaves and exact numbers
opaque. The compiler checks source correspondence and both proof roots; backend
ownership, resources and bytes have independent executable conformance tests.
Proof availability does not select a layout without comparable lifecycle costs.
See the distribution's `docs/private-sum-layouts.md` for capability and trust limits.

Maintained folds can additionally author checked scalar update and contribution
choices. `producers.cell_actions` and `producers.early_return` propose complete
action simplifications, admitted only through whole-action equality. Generated
helper names are bridged with ordinary induction theorems rather than hash-based
equality. See the distribution's `docs/maintained-folds.md` for trust boundaries.

Automatic typed probe authoring covers the complete admitted first-order wire
carrier family: scalars, exact U64/Int, Unit, fixed numeric vectors, lists,
inhabited recursive records, options/results, enums and identifiers. It derives
finite constructor choices and bounded nested collection sizes from declarations;
no source-function name or theorem ID selects cases. The JavaScript planner
measures advanced carriers through portable/compact boundaries using lossless
measurement packets. Unsupported trusted transfers and state lifecycles still
need their appropriate recorded evidence. Probe values and costs never grant
proof admission or permit skipping input checks.

`producers.indexed_lookup` proposes one U32/U64 map index per batch of ordered
membership queries. Map and filter callbacks, captured keys, duplicate keys and
output order are preserved by ordinary list induction and congruence proofs.
Query-dependent tables and float keys are outside the admitted domain. This does
not retain an index between public calls. Construction, memory and lookup costs
still need whole-workload evidence; proof availability alone grants no selection.

`producers.guarded_choices` composes whole-function equality proposals with a
checked `choose(count(input) >= cutoff, alternative, original)` expression.
The count is exact Int. The ordinary Cases/Use/Trans proof must establish both
branches; recipe provenance and cutoff values grant no equality authority.
Source-extension prefixes are retained. The author accepts concrete equalities
without remaining conditions/type parameters/assumptions, and bounds repeated
size-guard authoring. It does not cover retained state or arbitrary inner loops.

Published recipe data chooses base producers and cutoffs. The initial three
recipes wrap indexed ordered deduplication at 8, 128 and 2048 elements, using the
existing selection-size grid. The author also replays an unrelated Boolean-list
law in tests. Additional installed producers can be composed by database recipe
data without compiler or planner dispatch changes. Normal bounded planning and
whole-call measurements still decide selection; neither profitable selection nor
absence of small-input regressions follows from the branch proof.
