# Independent review of web proof batch 2

The baseline contains 732 canonical members at snapshot
`52f1b3564ceb41b36a12ae6fca2d067e1bd2a11ec64ab3556d31ef6cdd37e12b`.
The frozen `ink-sequence-proofs` compiler has SHA256
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
The reviewer verified these identities read-only. This lane writes only this
review and runs no compiler, tests, proof search or timed jobs.

## Initial candidate assessment

The previous executable catalogue already contains quadratic/cubic finite
difference maps and recurrences, bilinear decrement, partition invariance,
repeat identity/product/subtraction/cancellation, original-value restore,
map fusion, cross-type map fusion, map/right-fold fusion, self-zip addition,
filter fusion/idempotence and the 32 concat laws. New display names or another
proof term for those same statements do not constitute new enabled work.
Legacy collection/filter model entries are also present; name inspection alone
cannot establish whether they can actually rewrite a new executable source.

Potentially useful additions under the existing checker are a quartic finite
difference recurrence inside a direct map, and filter/right-fold fusion with a
concrete callback. The former may remove per-element arithmetic and repetition;
the latter may remove a filtered intermediate list while preserving exactly
the right-fold operation order, including F32. A combined map/filter/fold law
can remove two lists, with any duplicated callback work accounted for. Generic
curried callbacks need executable reification evidence; prior admission alone
has not guaranteed that selected source can be reified.

Every proposed benchmark function must apply at least one new member and have
a different selected body from the old-732 control. Byte duplicate checks,
alpha-equivalent statement inspection, checker admission, negative controls and
planner selection/replay are separate evidence. A difference in selected source
does not itself prove a latency improvement.

## Benchmark requirements

The previous harness captures one typed input snapshot per implementation,
includes Wasm input copying and output conversion, awaits runtime boundaries,
and consumes output values inside timing. Literal JS and Rust preserve source
operations and materialized stages, with ordinary JIT/release optimization
allowed. Any new control must preserve wrapping U32 arithmetic and the original
algorithm; an algebraically simplified implementation needs a separate label.
Allocation and input/output representations remain part of the measured caller
contract and must be described.

Independent Python oracles must cover empty/singleton/full-width inputs and
both relevant branches. Literal source recurrence evaluation should corroborate
closed forms. Exact contents are compared before timing; timed checksums consume
outputs but are not collision-free proof of equality. Original and checked GPU
variants must both execute actual shaders before reporting a two-shader gain.
CPU fallback records must remain visible and must never become GPU samples.

The previous audit gates on shader availability and `backend == gpu` while
retaining availability counters. Batch 2 should additionally require positive
dispatch counters and expected upload/readback byte counts for nonempty U32
workloads, including during timed calls. Empty-input validation has its own
counter expectations. Full-call GPU latency includes upload, dispatch, readback,
output conversion and consumption; first-call setup stays separate.

Use interleaved rounds and paired confidence intervals with explicit ratio
directions. Retain regressions and intervals crossing one. A result for a new
proof on one workload does not rank languages or establish universal
profitability. Preserve frozen artifact hashes, exact old/new snapshots, compiler
identity, raw samples, startup, warmup, calibration and fallback evidence.

## Final producer source and author evidence review

`web_compute2_laws.py` supplies 18 new laws: quartic/quintic differences,
increment recurrences and invariant recurrences for U32, I32 and U64. The
left-associated binomial expression equals `k^d` in each wrapping ring.
Subtracting that constant preserves the accumulator; adding it produces the
stated closed form for every natural count, including zero. The repeat index
is unused. No F32 algebra, condition, checker extension or backend rewrite is
introduced. These statements have different source patterns from the previous
quadratic/cubic laws.

`web_fusion2_laws.py` finally supplies 15 laws: filter/right-fold fusion and
mapped-filter/right-fold fusion for four numeric types; weighted self-zip
right-fold fusion for the same four; and weighted self-zip sum factoring for
three wrapping integer types. The F32 laws retain the exact multiply, add and
subtraction grouping and the accepted elements' right-fold order. There is no
F32 sum factoring. Pure predicates may run in a different schedule after
fusion; accepted mapped values may be multiplied twice rather than once.
That is a profitability tradeoff, not a hidden theorem premise. Five initial
filtered-concat-count candidates were excluded because default cost selection
did not apply them; their early admission receipts are not final batch counts.

The author evidence records all 18 compute and all 15 fusion laws admitted,
default-selected, replayed and reified. Old-732 controls leave representative
original source bodies unchanged. The reviewer inspected the final sources,
test code, logs and admission/command receipt structure read-only; the reviewer
did not independently rerun these jobs. Compute author tests: five passed.
Fusion author tests: three passed. Freshly hashed false controls erase required
compute work, change `k+d` to `k-d`, or invert a F32 filter guard; rejection is
semantic-normal-form disagreement, not a hash-identity failure.

Root reports publication of the checked 33-law union, 732 to 765 members, at
snapshot `7ecbce6e14b1273e771e4634b61e92d0f85929934c0d4e165b1f14c7c8660c6c`.
The immutable old snapshot and isolated discovery index remain the baseline.

## Six-task harness pre-measurement review

The final source uses three vector tasks (quartic repeat, quintic repeat and
quartic map) and three scalar tasks (weighted zip fold, mapped filter fold and
weighted zip sum). Repeat counts are 1024. Case dispatch in JS/Rust agrees with
the runner, while Ink calls by function name. Independent modular Python
closed forms and literal stages agree mathematically: fold signs depend on the
accepted-element index and parity, with the initial seed's sign retained.
Python literal scalar evaluation covers whole fixtures; recurrence evaluation
corroborates every boundary element and the first four per measured fixture.
The source controls preserve list stages, loop counts and wrapping arithmetic.

Two control choices should be explicit in the archived scope. Power helpers
reuse the computed `(a+k)` argument, a common-subexpression optimization within
the same algorithm. Rust writes vector results to a reusable preallocated Wasm
destination, while normal release/library optimization applies to its
intermediate Vec stages; a consumed mapped Vec may reuse allocation during
filter collection. These are implementation choices, not a closed-form
replacement. Cross-language ratios compare those concrete caller contracts,
whereas prior/new Ink ratios isolate the catalogue change under one compiler
and runtime. The root added singleton, no-accepted-item, all-accepted-item and
zero-factor CPU oracle fixtures before freezing, and explicitly disclosed the
power-helper and Rust-buffer choices in the archived scope. The audit now also
checks warmup/calibration checksums, normalization and GPU counter totals.

The fresh harness requires actual nonempty GPU vector calls to report exactly
one dispatch, `4*N+24` upload bytes and `4*N` readback bytes. The 24 bytes account
for two scalar parameters and four length metadata words, including the unused
seed parameter. Every timed call checks these counters; each sample archives
aggregates that the Python audit verifies against its iteration count. Manifest
eligibility and returned backend are checked, and scalar fallback stays outside
GPU timing. CPU empty-vector validation does not establish an empty GPU run.

Preparation uses the unchanged default planner with an old copied/indexed
store and a new copied/indexed store, replays both selections, requires a new
member per benchmark function and different old/new selected bodies, and
archives compiler and artifact hashes. Raw samples are interleaved by round;
ratios and confidence intervals have explicit directions. Output consumption,
host snapshots, Wasm copies and GPU transfer/dispatch/readback stay in timers.

No blocking semantic, oracle, control or GPU-gating issue was found in this
pre-measurement source review. The pre-freeze requests have been addressed.
Archived preparation metadata has now been inspected read-only: compiler and
732/765 snapshot identities match; prior selection has zero applications and
its wire module equals the original; all six checked bodies differ; each uses
one new law, with seven total applications including one existing law. All
archived artifact hashes match and preparation commands succeeded. Baseline,
prior and checked manifests have shaders for the three vector tasks, and
explicit CPU fallback reasons for the three scalar reductions. Thirteen
validation fixtures are archived. Completed timing results remain pending.
Proof correctness and actual application are supported by the author receipts.

## Completed Node results

Read-only inspection of `node-summary.json` and `node-results.json` confirms
36 cells, 2,772 measured samples, 1,254 exact backend comparisons over 13
fixtures, 177 Python literal checks and 144 Wasm memory observations. There
are no GPU samples in the Node result. The archive uses the reviewed compiler,
old/new snapshots, controls and full-call scope. Statistics were read from the
archived summary; the reviewer ran no timing or statistical recomputation.

Both repeated polynomial tasks show strong prior/new JS and Wasm improvements
on this machine. The collection representatives improve JS complete calls, but
Wasm profitability varies. In particular, mapped-filter-fold at small-1024 is
a supported regression: prior/new ratio 0.942 with interval [0.927,0.964].
Several other small/medium non-repeat Wasm intervals cross one. These results
must remain visible when evaluating the structural planner cost estimate.

The controls also prevent a general language claim: checked Wasm remains slower
than original Rust/Wasm for the standalone map and scalar collection controls,
despite database improvements to Ink. Recurrence elimination wins that concrete
comparison. All measured tasks are six U32 representatives; admission/replay
for 33 typed laws does not mean all 33 were profiled.

## Completed browser results and final assessment

The browser archive passes with 36 cells, 3,150 measured samples and 1,362 exact
comparisons over the same 13 fixtures. Its adapter identifies Apple/Metal 3.
There are 54 actual GPU variant/cells and 54 retained CPU fallback records for
scalar reductions. For full-4096 vector calls, availability reports exactly one
dispatch, 16,408 uploaded bytes and 16,384 readback bytes. Read-only inspection
of every archived GPU sample, warmup and calibration counter aggregate found
no mismatch against iteration count and expected input/output byte totals.
No scalar fallback became a GPU sample. All prepared artifact hashes still
match after measurement. The reviewer performed no timed job, compiler job or
confidence-interval recomputation.

The new recurrence proofs demonstrate supported complete GPU-call improvements
at full-4096: quartic repeat prior/new 1.538 with interval [1.453,1.568], and
quintic repeat 1.757 [1.734,1.848]. These are comparisons of two actual shader
variants, including transfer, dispatch, readback and output consumption. The
same two browser cells show JS ratios approximately 2515 and 2692 and Wasm
ratios 134 and 131. Those large CPU gains arise from eliminating the explicit
1024-step recurrence, not from a general advantage of one language.

The standalone quartic-map GPU full-4096 ratio is 1.000 [0.987,1.033]; it does
not establish a GPU improvement. There are real browser Wasm regressions:
quartic map at small-4096 is 0.984 [0.971,0.997]; mapped-filter-fold at
small-4096 is 0.967 [0.935,0.994]; weighted-zip-fold at full-32 is 0.939
[0.869,0.981]. Other intervals crossing one remain inconclusive. These results
are consistent with allocation removal or structural cost being an imperfect
predictor of complete-call latency, especially when mapped multiplication can
be recomputed and the host boundary dominates.

Checked Wasm still loses to the concrete original Rust/Wasm map and collection
controls while winning the recurrence controls. Direct JS/control ratios have
the opposite interpretation from prior/new ratios: values below one favor Ink,
and runtime-wrapper JS is a separate variant. The power-helper and reusable
Rust-output choices are explicitly disclosed, so these concrete control results
must not be presented as a comparison to every possible handwritten program.

Final independent review passes with these limits. The batch adds 33 admitted
and actually replayable typed laws; six U32 representatives were measured on
one machine across JS, Wasm and three genuine GPU vector workloads. It supplies
both new complete-call wins and useful regression/no-difference evidence. It
does not establish profitability for all laws, all typed instances, arbitrary
production programs or other hardware. Root owns final statistical/import
verification and the combined report; the original samples and selected
artifacts remain the evidence for any quoted result.
