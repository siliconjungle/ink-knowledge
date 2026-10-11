# Independent review of the web proof batch

This review separates equality of pure Ink values, the conditions of an actual
proof application, and measured backend profitability. A content hash, producer
name, successful search, or performance receipt does not establish equality.

## Scope and status

The reviewer inspected the existing executable semantic producers and target
boundaries without running tests, builds, proof search or timed workloads.
Both numeric and collection producer sources have been reviewed. For those
sources the reviewer read author checker receipts without running their jobs.
The reviewer subsequently authored and checked the eight Frontier-inspired
laws below; that lane is author validation, not independent review. Publication,
application replay and measured results remain separate stages of review.

The existing catalogue already supplies integer repeat addition, subtraction,
product, identity and cancellation; same-type map fusion and identity; mapped
count elimination; integer scaled/zero sums; constant filters; filter fusion
and idempotence. New names or differently named aliases must not inflate the
number of new canonical laws. Canonical byte identity and alpha-equivalent
statements both deserve inspection.

## Producer source review

`producers/web_numeric_laws.py` supplies 24 laws over U32, I32 and U64.
The quadratic and cubic finite differences equal `k*k` and `k*k*k` in the
wrapping word ring. The bilinear difference equals `-k*k`, and the partition
step equals its accumulator. Adding these constant differences or cancelling
them gives the stated repeat closed forms and invariants. Natural count zero
returns the original initial value in every repeat law; converting counts into
the word ring handles wrapped counts. Signed I32 uses the same modular bit
pattern arithmetic without introducing signed comparisons or division.
The final producer excludes the initial branch-increment candidates rejected
by the existing normalizer; their archived rejection evidence is not admission.
It instead includes a cubic invariant. There is no numeric F32 law.

`producers/web_collection_laws.py` supplies 20 laws: eight cross-type map
fusions, five same-input zip identities, four map/right-fold fusions and three
integer zero-map scans. The final zip rules use addition (Bool uses conjunction),
and the final fold rules map `x*k` then fold `x-acc`. Initial generic curried zip
and fold candidates were narrowed because selection reification did not support
their nested function applications. Cross-type signatures are outside the earlier
same-type map-fusion signatures. Zip uses the exact same list twice, preserving
truncation for empty and nonempty inputs. The fold lambda binds its head at
de Bruijn index one and accumulator at zero, retaining each map operation and
the exact right-fold application order. Its F32 case does not reassociate any
arithmetic. Evaluation of pure map callbacks moves into the right fold, which
changes allocation/evaluation scheduling but not their pure value results.
The final scan source maps `x-x` before scanning; a transitive proof passes
through the constant-zero map and returns that unscanned subtraction map.
It produces a same-length zero list and is limited to wrapping integer types.

The reviewer compared the finalized numeric isolated manifest and collection
isolated manifest against all 648 canonical snapshot member IDs: 24 and 20
distinct entries respectively, no overlaps with the old snapshot, and 44
distinct combined IDs. The old snapshot has 89 executable rewrite entries.
Inspection of the typed statements found no renamed duplicate of an existing
executable law. Structurally new laws do not establish that the old database
could never derive an equivalent optimisation; a pinned old/new search control
is needed to attribute additional planner reach.

The numeric checker receipt at `numeric/validation.stdout.json` admits all 24
final laws. Author receipts in `numeric/tests.log` and
`collection/validation.json` / `collection/tests.log` report three passing tests
per producer. The final numeric store is `numeric/final-store`; its old-648
control leaves six repeats while the new numeric store removes all six.
Collection admission and replay cover all 20 concrete applications in two
groups, with hash-valid false zip and reversed-F32-fold controls rejected.
The reviewer did not independently execute those jobs.

No producer-side semantic blocker or expansion of the trusted core was found.

## Semantic concerns to check

- Integer algebra must retain wrapping U32/U64/I32 semantics and the exact
  signed comparison domain. Mathematical integer division identities require
  explicit nonzero/range conditions and are generally not wrapping identities.
- Repeated overwrites and idempotent steps require the zero-iteration case.
  Elimination of a repeat's initial value is invalid when its count is zero.
- Index arguments to repeat and indexed map must retain their U32 behaviour;
  they cannot silently become unbounded natural values.
- Zip truncates to the shorter input. Rewrites that preserve just one input's
  length need equal-length premises or the exact same list on both sides.
- F32 composition may retain exactly the same primitive operations, but cannot
  reassociate arithmetic, assume NaN reflexivity, collapse signed zero, or skip
  separately rounded operations without a valid checked premise.
- Pure list traversal may change materialization and evaluation order because
  there are no effects. This does not establish equivalent allocation failure,
  resource limits, host input validation, or aliasing policy.
- Higher-order parameters, capture substitution and de Bruijn indices must
  retain their declared sorts under nested lambdas and induction hypotheses.

## Proof and publication boundary

The proposed objects should use the existing general equality checker with no
trusted theorem flags or special compiler rules. A successful checker receipt
must bind the exact law bytes. The publisher should stage the complete extension,
check it before updating the canonical snapshot, retain old immutable objects
and snapshots, and rebuild SQLite as a disposable discovery index. At least one
hash-valid false control should be rejected, and representative concrete planner
applications should be independently replayed.

Target lowering, the C/LLVM and JavaScript toolchains, WGSL shader emission,
device drivers and host transport remain trusted implementations. Checked source
equalities do not prove these implementations correct.

## GPU workload candidates and interpretation

GPU v2 accepts an array result whose outer operation directly maps, zips or
maps with an index over input arrays. Its literal scalar emitter supports
bounded repeat. Ordered scalar reductions, filters and nested collection
receivers are outside that GPU v2 path.

A same-input zip rewritten to a map is a useful possible catalogue gap: both
forms can be GPU eligible and truncation is identical. Do not assume fewer
uploads: the shader still binds every declared parameter, and actual upload,
dispatch and readback counters must establish the transport difference.

A proof applied inside a direct map's repeated scalar computation can compare
two actual GPU shaders. Use enough per-element work and array sizes to assess
the transfer/dispatch crossover. Shader compiler optimisation may already remove
the original computation, in which case a checked source law can be correct
without improving GPU full-call latency.

Nested map fusion can make an unsupported source GPU eligible. Such a result
compares source CPU fallback with checked GPU execution; it must not be described
as speeding up an original GPU shader. Record each actual backend and fallback
reason, and keep this eligibility experiment separate from two-shader timings.

## Measurement requirements

Use exact independent source oracles over empty, singleton and full-width inputs;
validate list contents and scalar results before timing. Compare source and
checked variants, original-algorithm JS/Rust controls with normal JIT/release
optimisation, and separately labeled algebraically matched controls. Materialized
ordinary-array and typed-array JS styles should be identified.

Full-call GPU timings must include upload, dispatch, readback and output
consumption; Wasm timings include its actual host transfer. Input capture and
the caller contract must be explicit. Separate startup/first-call costs, preserve
raw repeated samples, interleave trials and report paired confidence intervals.
No speed claim is supported when its interval crosses one. A proof is not a
universal performance claim, and a handful of kernels does not rank languages.

## Frontier lane and publication review

The eight Frontier-inspired laws preserve pure U32/I32/U64 values: guarded
same-value writes, repeats that restore the original value, and guarded folds
that preserve their initial value. Their names do not claim to verify complete
mutable or JSON patch operations. The pinned source mechanisms, exclusions
and exact proof families are documented in `frontier-notes.md`. No F32 equality
guard is admitted by this producer.

All eight were admitted and selected/replayed, with old-648 controls leaving
the original core unchanged. Two hash-valid false controls were rejected.
Three author tests passed; the old snapshot test was subsequently isolated in
a temporary rebuilt store so it does not disturb the canonical index after
publication. The final numeric24/collection20/Frontier8 union contains 52 new
laws. The root publisher advanced the catalogue from 648 to 700 members.
Publication stages checker validation before writing canonical bytes, records
source provenance and compiler identity, and preserves prior immutable snapshot
objects. SQLite discovery is disposable and does not supply proof authority.

The active frozen benchmark uses the exact pre-extension compiler and selected
artifacts. No generic performance conclusion follows from these receipts.
Concat is a subsequent general semantic extension, with its primitive trust
boundary and pending independent/backend validation recorded separately in
`sequence-semantics-plan.md` and the distribution's sequence semantics document.
