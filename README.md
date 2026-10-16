# Ink knowledge

Immutable knowledge data for [Ink](https://github.com/siliconjungle/ink-lang), with a rebuildable SQLite discovery index. Search and execution policy live in [ink-planner](https://github.com/siliconjungle/ink-planner); proof checking stays in Ink's independently buildable semantic core. Storage never grants proof authority.

`libraries/bit_automata.ink` provides ordinary packed bit-state source algorithms:
checked construction of 1..32-octet literal masks, non-overlapping matching and
explicit strided/transposed packed inputs. `bit-circuit-laws.ink` supplies eight
replayed scalar proof components, published under `bits/` with
`store/bit-circuit-view.json`. These proofs establish their scalar equations;
they do not certify an entire matcher, generated backend or implicit String
replacement. The distribution exposes the library as `std:bit_automata` and
retains matched benchmark sources and adverse/small-input controls.

`producers.function_correspondence` authors explicitly requested pairs of pure
functions as ordinary normalization laws, admitting their exact portable
contexts before publication. Two polynomial/nonlinear derivative-batching
correspondences are in `store/differential-batching-view.json`; fixtures and
negative source-attachment tests are under `tests/`. They compare those exact
generated implementations, not the correctness of the general AD transform or
any backend. The stored equations do not make an automatic profitability choice.

## Storage contract

`ink_knowledge/automatic-selection.json` owns bounded pure-call probe sizes,
distributions, measurement controls and the required profitability margin.
`selection_probes.create(core)` authors probes from supported exact typed
signatures and source constants; it does not use function names or theorem IDs
to choose behaviour. Unsupported transfers and state/action/event
lifecycles decline. Synthetic probes are workload proposals, not observed user
usage or correctness evidence. Contract support roles are taken from checked
metadata, so generated checks and implementation bodies do not receive duplicate
synthetic usage. Bounded `seed_cases` add constructor-sized proposals for guarded
entries; they do not imply the guard holds. The planner runs the original checked
ingress guard and filters only false proposals, retaining every requested phase
and binding observations to the actual retained inputs. Supplied workloads remain
strict; a phase with no admissible proposal retains the baseline. Planner
measurement and proof checking remain separate. `ProposalViews.update` refreshes authenticated proposal membership for
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

`store/trees/` contains authenticated sorted leaves of at most 64 IDs and binary branch nodes. `store/snapshots/<id>.json` pins a Merkle root; `store/publication.json` atomically selects the current snapshot and the hash of its immutable alias map in `store/names/<id>.json`. A bounded exported view carries selected roots, their exact dependency closure and membership proofs. The core authenticates membership, hashes, semantics, proof terms and applicability. It never needs the complete database. New snapshots do not invalidate replay of a plan carrying an older pinned view.

Publication serializes writers with a private SQLite transaction at
`store/.publication.sqlite` (a coordination file, never a proof or index).
Keep that file at its stable path. Acquisition waits at most 60 seconds; process
exit releases the operating-system lock. `extend` checks its expected snapshot
while holding the lock and reports a conflict if another writer has changed it.
Retry a conflicted extension from a freshly opened `Store`; historical explicit
pins remain read-only. Complete replacement publication remains an explicit
replacement, rather than an automatic merge. Temporary proposal transports use
the same coordination when publishing their membership trees.

Immutable files are completed privately and linked into place without replacing
an existing path. Concurrent identical creators can both succeed; differing
bytes report a collision. Readers capture the small publication record and load
its hash-checked names lazily through `Store.names`. `Store.publication_id` binds
both snapshot and names, so names-only changes are visible to staging and copy
checks. `Store.is_published(root)` checks the selector rather than a mirror.
`Store.publish(..., expected_publication=id)` checks that generation under the
writer lock before replacing it; ordinary `publish` remains explicit replacement.

The old `names.json` and `snapshot.json` files are recoverable mirrors. Writers
bootstrap the old selector before changing either mirror, then commit through one
atomic selector replacement. A precommit error leaves the old generation selected;
rollback attempts to restore mirrors. `Store.recover(root)` or the next publication
restores them after a killed writer or persistent write failure. Raw mirror readers
can still observe an uncommitted pair and must use the Store API for current reads.
Malformed selectors or altered immutable name maps fail rather than falling back.
These guarantees cover concurrent visibility and process interruption, not power
loss durability; this protocol does not fsync files and directories.

An explicit snapshot path still means those exact file bytes, including historical
pins, independently of the current selector. A snapshot does not pin display names:
for an explicit pin, `Store.names` captures current aliases on first access and
filters them to that snapshot's membership. Use content IDs for durable references.
Names and selector hashes never establish proof authority. Content, membership and
proofs still authenticate on retrieval and admission. Corpus isolation installs the
captured pair, checks the complete generation identity, and omits coordinator and
temporary publication files.

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

`ink_knowledge.law_templates.from_general(store, law_id)` exposes a stored
polymorphic semantic law as an indexed template. The template uses the original
law through snapshot-authenticated `fixed_dependencies`; concrete instances
still replay ordinary proofs. This factory refuses laws with unproved conditions
or assumptions. It introduces no compiler rule or algorithm-specific matcher.
`libraries/independent-fold-batching.ink` uses this path to batch independent
folds while retaining each state's exact operation order, including floating
arithmetic. Its supporting map lemmas are proof dependencies, not automatically
enabled search rules. Profitability remains a separate measured decision.

`producers.captured_fold_batching.templates(map_fusion_id)` authors a source
algorithm that lifts per-result captures into a private environment/accumulator
record before batching, then projects the results. The generic source-template
producer shares the law-template adapter builder, so callback abstraction,
source extension and proof composition need no batching-specific compiler path.
Inputs that vary by environment do not match the shared-input rule. A normal
planner run can discover the alternative, but needs cost evidence to select it.

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

`producers.indexed_lookup` proposes shared U32/U64 map indexes for batches of
ordered membership queries. Membership can occur inside record results, Boolean
conditions and nested callbacks; all observations of the same independent key
list share one index. Distinct key lists remain distinct indexes. Ordinary list
induction, function extensionality, congruence and ordered-word case proofs retain
the complete callback result, captured keys, duplicates and output order for left
and right folds, including
reversed equality/disjunction operands. Fresh bindings prevent capture. Discovery
is bounded to four key lists and 128 observations per callback; budget exhaustion
retains the source. Query-dependent tables and float keys are outside the admitted
domain. Indexes do not persist between public calls. Construction, memory and
lookup costs still need whole-workload evidence; proof availability alone grants
no selection. These are database-produced proofs, with no new compiler rule.

`producers.guarded_choices` composes whole-function equality proposals with a
checked `choose(count(input) >= cutoff, alternative, original)` expression.
The count is exact Int. A generic database theorem proves
`a = b => a = choose(p, b, a)` through ordinary Cases/Use/Trans rules. The producer
instantiates that theorem instead of defining its proof in compiler or planner
code. Its `equivalence` parameter can select another theorem from the pinned
snapshot; the installed default is `ink_knowledge/guarded-choice-law.json`.
Every selected theorem and premise replays; recipe provenance and cutoff values
grant no equality authority.
Source-extension prefixes are retained. The author accepts concrete equalities,
retains their conditions and application premises, and bounds repeated size-guard
authoring. General type parameters and assumptions must be instantiated first.
It does not cover retained state or arbitrary inner loops.

Published recipe data chooses base producers and cutoffs. The initial three
recipes wrap indexed ordered deduplication at 8, 128 and 2048 elements, using the
existing selection-size grid. The author also replays an unrelated Boolean-list
law in tests. Additional installed producers can be composed by database recipe
data without compiler or planner dispatch changes. Normal bounded planning and
whole-call measurements still decide selection; neither profitable selection nor
absence of small-input regressions follows from the branch proof.

Automatic selection probes partition variable-width inputs into bounded,
contiguous size groups before timing them. `automatic-selection.json` controls
the phase budget and tolerated demonstrated phase regression. All original calls
are retained; each function/transfer boundary retains its total expected-call
weight. Integer allocation uses largest remainders and reports the exact rational
weights, rounded weights, and any size groups merged by the budget. This measures
synthetic width regimes, not every possible distribution or input combination.

Automatic JavaScript and Rust acquisition use the database policy's bounded fresh-process
count (currently three). Its larger batch cap lets short calls reach the timing
floor more often; reaching the cap still does not guarantee a minimum duration.
Processes vary the deterministic interleaving seed. Process identity and every
sample remain in the receipt; these are development measurements, not proofs.


Template discovery can expose leading lexical `let` bindings through bounded,
capture-avoiding beta reduction. The index retains every original site and adds
optional normalised search views within its existing node budget. Matching those
views emits an adapter whose left endpoint is the exact original expression;
ordinary `Normalize` and `Use` proofs still replay in the kernel. Exhaustion drops
only optional views. Open local variables remain ineligible for a closed adapter. Instantiated
conditions remain explicit obligations, including through enclosing expressions. This does not change compiler semantics, install
an optimisation automatically, or imply a performance gain. `test_head_beta.py`
checks indexed discovery, capture avoidance, resource exhaustion, concrete proof
replay, forged results and word/float output parity. After exposing a leading
binding, discovery can also find a law inside an enclosing expression without
crossing another lexical binder. The adapter lifts `Use` through ordinary
`Congruence` and retains the complete original source endpoint. This composes a
fold law through record projections or arithmetic siblings without teaching the
compiler a special projection/fold optimisation. Context traversal and aliases
share the bounded discovery budget; arbitrary rewriting beneath binders remains
outside this adapter's scope.

`producers.word_facts` performs bounded, untrusted unsigned-word analysis during
offline discovery. Facts established by a `choose` condition apply only inside
that arm. Supported comparison bounds, Boolean negation, true conjunctions and
false disjunctions refine local scopes; nested constraints intersect, while
alternative arms union possible values. Wrapping operations retain their fixed
meaning. Contradictory constraints are conservatively discarded, not used as
proofs of unreachable code. This is expression analysis, not a whole-program
control-flow analysis or an assumption that a fallible contract always succeeds.


`analyse_candidates` returns facts and proposals in one synchronous discovery
query, avoiding a second traversal of the root. Reuse is bounded to 2,048
non-leaf entries, 16,384 node/scope references and a conservative 1 MiB record
charge (not an RSS limit). Each key binds the exact source node and branch
scope; strong references prevent identity reuse. Cache hits charge the original
logical node visits and relative depth, so reuse cannot bypass analysis limits.
The query clears all records on success or failure. The streaming `candidates`
API retains no memo across yields. Callers must not mutate input during a
synchronous query. These facts remain untrusted; each rewrite still needs proof.

Offline `ink_planner.llvm_learning --proposal-engine facts` proves the complete
guarded replacement before publishing any law. The reusable `bounded_low_mask`
u32/u64 laws additionally allow symbolic masks under the checked condition
`m & (m + 1) == 0`, including zero and the full word mask. Their universal
certificates are stored with the other word laws. A use with an arbitrary mask
cannot discard this premise; source-level selection still replays it. These
changes add discovery/proof opportunities, not runtime adaptation or a claim
that every selected simplification improves an application's measured speed.


Higher-order exact-source adapters retain instantiated conditions from their
base law. Each base-law use refers to the corresponding adapter hypothesis;
ordinary selection must still prove every adapter condition at the source site.
A discovered callback match neither supplies a premise nor allows it to be
omitted. This supports conditional callback laws through the existing generic
instantiator and checker, including renamed parameters and concrete type instances.
Disposable pattern-index queries also enforce the public store's 0–1024 page
limit and explicitly close failed reader opens; these are discovery resource
controls, never mathematical authority.

The default planning registry includes global and modular semantic search as peer
rewrite recipes. Modular search delivers the checked best combined prefix after
each improved function, keeping its output bounded by the function count. Neither
recipe names algorithms or grants priority to a theorem; both discover installed
laws and require complete source equality. Their structural scores rank search
hypotheses only. Existing measured whole-workload selection decides profitability,
and can retain the baseline when no comparable profitable evidence exists.

Modular semantic discovery also offers checked guarded versions of its completed
selection at the database's existing count cutoffs (8, 128 and 2048). Each eligible
independent whole-function rewrite uses the conjunction of all its List parameter
bounds; the other branch evaluates the original expression. Original equality
conditions and external premise roots remain explicit. Repeated rewrites and
interior paths first propose whole-function equalities using ordinary transitivity,
congruence, explicit lambda extensionality and branch cases. Both application
arguments and premise terms retain their binder scopes. The composed proof must
replay; unsupported ambient contract or known-argument facts can still decline.
The cutoffs propose alternatives; measurement must establish profitability. A
guard's existence does not promise a win on small inputs.

The installed `producers.common_subexpressions` producer proposes explicit lexical
sharing for exact repeated pure scalar terms. It keeps callback scopes separate
and preserves captured de Bruijn references when inserting a binder. These are
whole-function source-bound `Normalize` laws using existing application/lambda
syntax. Proposal size and count bounds grant no correctness or profitability
authority; original and shared alternatives remain available to generic search.

Source word certificates can opt into `--semantics fixed-words-v2 --encoding
shared-v2` during offline `author_word_identities` acquisition. Fixed rotate
meanings are reconstructed by the versioned source circuit; matching shift/rotate
identities remain untrusted database proposals. Legacy source semantics and
literal encoding stay the defaults. The certificate producer retains its chosen
gate encoding, and every resulting law replays in the independent core. Scalar
sharing also keeps lazy choice/Boolean regions separate.

Guarded parameter-cache authoring extends `producers.representations` with
`--cache-query NAME --cache-arguments '[7,true]' --preserve-cache`. One exact tuple
of one to four U64/Bool arguments gets a maintained reply; an exact scalar guard
falls back to the original query on every other tuple. Ordinary universal source
representation, rollback, snapshot and migration proofs still replay; explicit
Boolean splits and bit-vector witnesses justify specialization. The
`guarded-parameter-cache` recipe seeds at most four bounded boundary/source-literal
proposals, with no hotness premise or automatic profitability exception. Repair,
compact-protocol and replacement composition currently decline. Parameterless
proposal bytes remain unchanged. See `tests/test_parameter_cache.py` for admission,
rehashing controls, exact scalar bounds and legacy packet identity.

The `loop_invariants` producer proposes scalar lexical hoisting from strict
regions of non-stopping map/filter/left-fold/right-fold callbacks. It keeps an
explicit empty-list guard and shifts nested captures hygienically. Existing
source binding and Normalize proofs must accept every whole-function proposal;
structural ranking and candidate bounds provide no correctness or profitability
authority. Conditional-only work and early-stopping callbacks are excluded.

Hoisting currently requires reviewed numeric/list operation trees. Nested string
construction and unanalysed source helper calls are declined even when the outer
result is scalar. This restricts proposal scope; it does not add an equality axiom
or treat a guessed totality fact as a proof premise.

`producers.point_delta.normal` keeps a bounded cache of successful call normal forms
inside one invocation, after 32 helper expansions. Exact argument structure,
function identity and remaining depth distinguish entries; registry/mode changes
in later invocations start fresh. Hits return fresh JSON containers. Small,
unsupported or oversized values continue through ordinary authoring computation.
This reduces repeated helper-DAG expansion, never caches proof verdicts, and does
not change Convert replay or its budgets. The V8 source pass records repeated-DAG
and captured-obligation controls separately from compiled runtime performance in
the distribution's `bench/v8-learning/normalizer`.

`producers.conditional_facts` discovers whole-function unsigned equalities from
known bits, ranges and one excluded value. Relational comparisons refine both
operands, and excluded points survive wrapping addition/subtraction/XOR with a
constant. Offline acquisition constructs and replays RUP proofs before publishing
laws or adding them to the existing word-identity proposal catalogue. The
`store/conditional-facts-view.json` contains four admitted examples. This is
inspired by Freerange's range/requirements approach; it adds no trusted inference
premises, general floating-point domain or runtime profitability exception.

`libraries/autodiff.ink`, `libraries/neural.ink` and `libraries/learning.ink` are
ordinary authored source for prepared reverse graphs, ReGLU network construction
and explicit F32 Adam state. The distribution exposes `std:autodiff`, `std:neural`
and `std:learning`. These add algorithms, not equality or approximation authority.
Hard-step/index estimators and sparse zero-cotangent behavior are explicit policy;
high-level VJP/MSE computes a fresh forward run. They are inspired by the pinned
MIT-licensed Handwired numeric runtime and learned gallery, with independently
authored Ink code. Reverse order, F32 moment arithmetic and source-opaque graph
validation have their own stated meanings; they are not bit parity with every
upstream interface or a general AD correctness proof. The companion typed-callback contract packet was regenerated through ordinary
proof replay: 23 obligations and 14 newly published canonical objects.
`store/typed-callback-contracts-view.json` retains that source-bound view; its
publication receipt distinguishes these contracts from AD-correctness claims.

The current recipe catalogue also retires an older unaliased `maintained-folds`
configuration that conflicted with the explicit current registry. Historical
snapshots retain its object. `store/recipe-discovery-repair.json` records both
identities; this repairs discovery and grants no proof or profitability authority.


`libraries/learning_session.ink` adds ordinary model/observation-generic continuous
sessions: bounded ordered feedback, explicit overflow/discard, source work budgets,
pause and publication cadence, serving/candidate separation and ticket/base-version
checks. The model type carries the complete optimizer chosen by its application.
Cancellation retains observations for an explicit restart. These algorithms grant
no AD, convergence, equality or profitability authority. The canonical proof
snapshot is unchanged by this source-library addition; the distribution retains
cross-target session checks, compiled durable recovery and the frozen-corpus audit.

`libraries/policy_gradient.ink` supplies generic categorical score-function learning,
masked choices, authored returns/baselines and trajectory gradients. Applications
provide masses and derivatives, random inputs, rewards, constraints and versioned
feedback. The distribution retains independent finite differences, contextual
learning, exact Adam resume and cross-target execution. This is F32 authored source,
not a compiler objective, exact-real sampling proof or convergence guarantee. The
canonical proof snapshot is unchanged by this library addition.

### Prepared binary64 text geometry

`libraries/prepared_text.ink` ports Pretext's simple prepared counter and geometry
walkers as ordinary source (`std:prepared_text` in the distribution). Immutable
measured data is separate from varying widths; count/height and complete cursor
observations have distinct execution paths. F64, shape/capacity validation,
explicit rejection of complex break kinds and the upstream license are retained.
This is not font measurement, full Pretext fidelity or upstream speed parity.

`libraries/prepared_complex_text.ink` adds complex prepared geometry under the
same explicit measurement boundary. Numerical profiles govern hyphen retreat,
tab stops, hanging spaces, padded openings and hard breaks; optional rich-inline
facts remain ordinary input data. Source validation bounds complete shapes,
finite measurements, work and cursor progress. The distribution retains an
upstream-only geometry/continuation oracle, cross-target state histories and
diagnostic performance controls. This source library grants no rewrite authority
and changes no canonical proof snapshot. Segmentation, shaping, measurement,
incremental preparation and the requested speed parity remain separate work.

The structural-price resource declares maximum-arm lazy choice work and
zero-cardinality branch hypotheses for equality/inequality against `count`.
These affect search ranking only; the planner interprets them in local lexical
contexts and does not export them as source proof facts. Both complete equality
replay and comparable lifecycle evidence remain required. See the distribution's
`bench/v8-learning/branch-cardinality` for default-discovery callback controls,
native acquisition and a rejection-only holdout.

Range-guided word conversion proposals now reuse the existing unsigned analysis:
`widen(narrow(x))` may return `x` only when its branch-local complete range fits
U32; the inverse U32 round trip is always lossless. Bounds on a wrapping sum
apply to that sum, without being inverted into bounds on its input. The existing
whole-function conditional-fact acquisition still exports ordinary checked
bitvector equations. Three frozen whole-branch conversion laws are available
through normal V8 word-library discovery, including relational and wrapped-sum
forms. Physical representation equality grants no range or check-elision fact.
See `tests/test_range_conversions.py` for independent boundary values, renamed
normal discovery and cross-branch forgery rejection. Profitability is measured
separately; these proposals do not select a runtime implementation by themselves.

Frozen structural specialization now retains transparent fixed-data definitions
in its checked evidence closure, including roots no surviving action reads.
The distribution derives their exact meaning from immutable source rows; the
producer supplies no additional premise. Tests specialize complete finite
64/128/232/512-element parameter results, preserve live updates and exact
checkpoints, and reject a changed value. This relies on the distribution's
shared frozen-literal projection and exhaustive-case proof checking. Long action
continuations and general graph/tape specialization still need further work;
this adds no automatic profitability or approximation authority.

The V8 floating library supplies fifteen checked F32 bit-cast, sign,
classification and IEEE self-comparison laws through ordinary indexed discovery.
It requires the distribution's explicit `fixed-scalars-v3` circuit semantics;
proof bytes replay independently with the existing resource limits. Bit identity
and IEEE equality differ for NaNs and signed zero. Always-false comparisons keep
strict operand evaluation through a bound application. Unsupported floating
arithmetic stays opaque and F64 semantic proofs reject. These are reusable
source laws, not a floating fast-math mode or automatic profitability decision.
See `tests/test_v8_float_laws.py` for payload/boundary oracles, mode substitution,
a rehashed false IEEE claim, callback scope and retained failing work.

`producers.closed_data_bridges` now factors exact closed-data equalities into
ordinary source-bound theorems. A later transparent chunk reuses prior lemmas;
complete action proofs retain data sharing even when literal syntax differs.
Candidate fingerprints and membership grant no proof authority. Discovery work,
depth or size exhaustion discards partial objects and retains the prior checked
tactic. Tests cover complete exceptional F32 lists through 512 values, a changed
NaN payload after rebuilding the candidate closure, authenticated invalid
theorems and transactional discovery fallback. These generated proof views ship
with selected models; the default canonical catalogue remains unchanged.

Source-call unfolding binds the complete formal parameter list once, in source
order, before entering the body. The ordinary lambda/application representation
keeps unused arguments strict and shares repeated U64, scalar and composite
arguments without a carrier whitelist. Lazy caller branches retain their own
boundaries. Ordinary source-bound Normalize proofs and selection checking remain
mandatory; the general checker compares lexical beta steps before expanding
unchanged helper arguments. Discovery/resource limits and measured profitability
remain separate. See `tests/test_inline_laws.py` and `tests/test_strict_inlining.py`
for independent execution-order traces, large unused input work, fresh binder
scopes and a changed definition rejected even after rebinding the source hash.

`producers.frozen_composition` now proposes conservative typed helper extensions
followed by complete action equality proofs. Small closed `foldl` computations
become leaf helpers; a balanced tree composes them without a linear continuation
stack. `producers.fold_chunks` authors ordinary cons/prefix equations and their
ordered composition, preserving dynamic inputs and exact numeric operations.
The explicit producer checks the entire two-step plan before atomically publishing
it. Generated proof views remain local to that plan, with no default catalogue or
automatic profitability change. Wrapping-word tests and complete 32/128-operation
F32 histories exercise the mechanism. `producers.frozen_build` chooses this
bounded authoring strategy when it produces helpers and the direct producer
otherwise. Normal trained-artifact publication replays and binds either format;
failed construction/checking never silently changes strategy. General graph/tape
specialization and automatic profitability remain further work.


Generated frozen helpers now share exact typed bodies modulo parameter and
lexical binder spelling. Callee/free names, literal bits, operand order, types
and scope remain part of the proposal key. This shares code, never returned
values or evaluations, and every resulting extension/action equation still
replays normally. The repeated 32/128-operation examples need 3/5 definitions
instead of 7/31; unique word chunks retain separate definitions. The standalone
producer accepts `--helper-layout shared|expanded`, with shared as the default;
both are explicit, proof-checked layout proposals, not profitability authority.

`producers.v8_integer_laws` proposes checked U32/U64/I32 division and remainder,
signed bit operations and power-of-two strength reductions. Only indexed frozen
proofs enter default discovery; unadmitted authoring attempts remain excluded.
The explicit `fixed-scalars-v4` proof mode reconstructs fixed wrapping/signed
operations and checked division/default meanings. Ordinary RUP replay and generic
bounded word extensionality establish equalities, including every covered bit;
solver outcomes and V8 provenance grant no authority. Typed lexical bindings
retain unused/repeated strict operands and lazy exceptional defaults. See
`tests/test_v8_integer_laws.py` for the independent formula/trace oracle,
source application, default discovery and adversarial proof replay. Correctness
admission does not establish a profitable implementation choice.

Frozen-library discovery builds disposable operator/constructor buckets per
immutable subject and applies exact sort filtering before the existing matcher.
Root formal parameters retain all sites of their sort; literal values, repeated
parameters and lexical capture checks still reach the exact matcher. Traversal
order and duplicate sites are preserved, and a changed subject rebuilds the index.
Only matched metadata triggers proof decompression; content/index consistency and
ordinary kernel replay remain mandatory. No index, cache key or head label grants
an equality, condition or profitability fact.
