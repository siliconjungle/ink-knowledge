# Independent review of web proof batch 5

The immutable baseline is the 809-member snapshot
`388e3ebd2714c88bc66ae9219102284162f4f65cbed359283f54896b3cfac87c`.
The frozen compiler remains SHA256
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
This lane writes only this new review, preserving all previous archived receipts.
No compiler, proof search, build, test or timed jobs run in this lane.

## Discovery and semantic constraints

Mapped-head lookup is a useful traversal-elimination model:
`xs.map(f).at_or(0,f(z)) = f(xs.at_or(0,z))` for a pure unary callback. Empty
input requires the mapped fallback, not the untransformed fallback. For a cons
list, the fixed zero index selects the mapped head directly, independent of the
tail. Generic callbacks can include cross-type maps if sort/reification support
permits; concrete arithmetic examples retain exact expression order for F32.
The source evaluates a full mapped list, while the target evaluates one callback;
this changes pure operation scheduling and resource use rather than element
value semantics. The existing `at_or` definition returns fallback for Nil and
head for Cons/Word(0), so no new trusted primitive or optimization rule is needed.

An optional indexed-head model selects only the first mapper branch:
`map_indexed(i,x => choose(i==0,x*k,x+seed)).at_or(0,seed*k)` can target
`at_or(xs,0,seed)*k`. This is a proposal requiring actual checker admission and
executable reification, not an accepted or measured rule. It avoids index casts
and separates index-zero behavior from arbitrary later work.

Catalogue discovery finds existing `performance/filter_idempotent_*` and
`filter_fusion_*` rules for all five primitive element types, plus old mapped
filter/count families. Duplicate-filter elimination is therefore not a fresh
family merely because a new producer or name is used. Core `count` returns a
wrapping U64, so a proposed minimum-of-counts zip shortcut cannot silently assume
unbounded list lengths fit that word. Each final source must remain unchanged
under pinned809 and receive a fresh default-planner application, locally replayed
and reified. Hash or repository membership alone does not establish correctness.

Scalar head kernels may explicitly fall back from GPU. Their target computation
can be constant work while the full-call input snapshot and Wasm ingress still
scale with source length. Benchmarking must retain that complete-call contract
and avoid presenting CPU head elimination as an actual GPU shader gain.

## Final terms, receipts and source controls

The final lookup producer contributes twelve concrete instances: scaled head,
affine head and threshold head across U32/I32/U64/F32. Threshold outputs Bool;
the benchmark wraps its result with `choose(...,1,0)`. Mapped fallback, zero-index
lookup, element order and each head expression are exact, including F32. The
generic callback theorem admitted but its `apply(f,z)` fallback could not match
ordinary inline source in the structural planner; attempted source spellings
were also unsupported. Those experiments are preserved and excluded from the
final batch, which uses executable concrete expressions without checker changes.
The optional indexed-head model is not part of this batch.

The reviewer read three passing lookup author tests and their assertions for all
twelve admission/default selection/replay/reification cases, fresh endpoints and
IDs against pinned809, and zero old applications with unchanged original bodies.
Thirty-six original/selected interpreter frames agree with independent expected
values, including empty/nonempty and overflow/signed inputs, F32 negative zero
and unused exceptional tails. Two hash-valid false controls (index one and
unmapped fallback) reject for differing semantic normal forms.

The reduction producer contributes thirteen laws: ignored-head right fold for
U32/I32/U64/F32; discount and spread sum factoring for three wrapping word types;
and scalar `x*k-x*d = x*(k-d)` for those word types. The fold returns its exact
initial seed without arithmetic, including F32 signed zero/infinities/NaN bits.
Word-ring distributivity preserves modular totals and empty-list zero. F32 sum/
factor reassociation is excluded. Six passing author tests cover all typed
admission/default selection/replay/reification, fresh endpoints/IDs, literal
versus independently reduced word oracles, actual original/selected interpreter
outputs and four hash-valid false controls. Every reduction evidence hash matches.
Old809 applies zero laws and preserves its author U32 core at
`ca928b2915d95dc3aede7fa6f76f644e2188aea473cf9da1cfced15584b11519`;
the author union822 selects one fresh law for each of four U32 representatives.

All seven benchmark kernels match handwritten original JS/Rust and literal
Python stages. The threshold first-read compares the original first word to seed,
or uses `k<seed` for empty input; the public U32 result is exactly 1/0. Other heads
use transformed seed fallback. Ordered reductions wrap every operation, while
the independent Python oracle reduces arbitrary-integer closed forms once per
result. Preflight records 91 complete handwritten-JS comparisons and 124 literal
Python checks. No reviewer test/compiler jobs ran.

Original controls retain mapped intermediates, first reads, reductions and
ignored-element folds in source, with ordinary JIT/Rust release optimization
allowed to remove unused work. Scalar Rust exports return one output word and
the driver reads `output[0]` as U32; vector spread returns its full length. Input
and final output destinations are preallocated/reused, whereas source Vec
intermediates retain ordinary library semantics. An expert directly written
head-only or already-factored control is unmeasured.

Full-call timing pays one entire typed-input snapshot, applicable Wasm ingress,
public result conversion, awaited boundaries and checksum consumption. Exact
output and original-input nonmutation checks precede timing. Head/ignored-input
computation can become constant work while the bridge remains O(N). Scalar GPU
fallbacks are explicit; spread-map supplies the meaningful actual old/new shader
comparison. GPU trial, warmup and calibration counters require one dispatch,
upload `4*N+24` bytes and readback `4*N` for the vector output. The reusable gate
also supports a one-word scalar result if a future emitter legally supplies one;
this is not evidence such a shader executes in this batch.

## Frozen preparation

Read-only frozen inspection passes all 72 artifact hashes, compiler/methodology
hashes and active/frozen source/control bytes. The 834-member catalogue is
snapshot `2e4106786af6f3cd41dbad39438c52dd9d518397b7a69b2841a525959c994f34`.
The old809 replay applies zero laws and preserves original core SHA256
`e45a688f4ebbb2c32f0346c1fd8e9d9a3c58ee2aa07bc739a1156bcc31e2ddbf`.
Seven fresh applications change all seven bodies; checked core SHA256 is
`a92cb3b7a10b2a236bffe104f3cb6c31ec165c9b7e1dbca862cfbfbf92abff31`.
The reviewer separately compared archived original/prior/checked bodies. All
preparation commands succeeded and full CPU validation passed.

All three frozen bundles use schema v2 because this mixed source includes head
lookup and a vector function. Only spread-map has a shader, in original/prior/
checked outputs; the six scalar functions retain the v2 array-result fallback
reason. This is a property of the measured mixed-bundle route. The standalone
legacy-v1 scalar sum route is not measured, so these fallback records do not
establish that scalar reductions are universally unsupported on GPU. Frozen
scope must remain unchanged for timing; a standalone route is separate future
evidence.

## Completed measurements

Post-measurement inspection again passes all 72 frozen hashes and compiler/
methodology identities. Node archives 3,234 timed samples and 1,463 exact
comparisons; browser archives 3,360 samples and 1,589 comparisons, totalling
6,594 timed samples. Both hosts have 42 cells and 168 measured Wasm observations.
The seven U32 representatives use small/full-width inputs at sizes 32/4096/65536;
the 25 typed proof instances are checked, but not all are profiled. Hardware is
Apple M2 with headed Chrome 154/Apple Metal-3 for GPU execution.

Independent raw inspection checks every saved trial, warmup and calibration
checksum and per-call normalization, GPU counter aggregate, actual-backend
availability record and raw/summary median. No discrepancy is found. Browser
has 18 actual GPU variant/cells, 126 timed GPU rows, and 18 GPU rows in each
warmup/calibration archive. All 108 scalar GPU-request fallback records remain
excluded from GPU samples. Only spread-map has comparable original/prior/checked
shaders. Root separately recomputes all 792 saved paired intervals exactly;
the reviewer reads that passing receipt rather than regenerating intervals.

Same-backend classifications agree with the profitability receipt: 181 supported
improvements, 53 inconclusive and 24 supported regressions across 258 comparisons.
Node runtime/direct JS each have 36 wins/6 regressions, with Wasm 14 wins/
28 inconclusive. Browser runtime/direct JS each have 36 wins/6 regressions,
Wasm 22 wins/20 inconclusive, and comparable GPU 1 nominal win/5 inconclusive.
Every adverse comparison is spread-map on runtime/direct JS: all six shapes
regress on both hosts. At full65536, prior/new runtime JS is Node
0.54699 [0.52487,0.65122] and browser 0.78333 [0.76111,0.85035]. Direct JS has the
same adverse pattern. The word-factor proof remains correct, but this emitted
form is slower for JS on the measured matrix; retaining the prior candidate is
appropriate for these cases. A smaller arithmetic operation count is not a
profitability proof.

The six scalar rewrites have supported JS gains throughout the matrix. Browser
full65536 runtime ratios are scaled-head 21.535, affine-head 29.403, threshold-head
30.680, discount-total 12.297, spread-total 12.286 and dead-map-fold 29.937, with
all intervals above 1. Corresponding browser Wasm ratios are roughly 1.11–1.18
and supported on this large fixture. Target head/dead-fold compute is constant
work, but the full input capture/ingress contract remains O(N); these are warm
complete-call improvements, not constant-time transport or startup measurements.

Spread-map's large GPU prior/new median is 1.0160 with interval
[1.0000000000735,1.12245]. The automated strict test nominally counts it as a win,
but its lower endpoint is essentially 1 and the baseline/new interval crosses 1.
This is borderline exploratory evidence, not a robust broad GPU improvement.
The other five GPU intervals cross 1. Individual 95% intervals across this many
comparisons are unadjusted for multiplicity.

The current routing receipt matches saved summary medians and all 12 current
CPU/GPU paired intervals across six spread-map cells. Both CPU routes are faster
than GPU in all 12, with maximum upper interval bound about 0.8280. Descriptive
lowest current medians across all 42 browser cells are JS 34 and Wasm 8; the
receipt does not supply paired JS/Wasm intervals establishing those median route
choices. Scalar fallback is limited to this mixed schema-v2 bundle; a standalone
legacy-v1 sum route and GPU-resident/fused pipeline remain unmeasured. No automatic
target-specific routing or proof-selection policy is implemented.

Checked runtime and direct JS beat original-algorithm JS controls in all 42 cells
on each host, despite spread-map losing against prior generated JS. Checked
Wasm versus original Rust-Wasm is mixed: Node 1 supported win/35 losses/
6 inconclusive; browser 7 wins/32 losses/3 inconclusive. Original Rust source can
optimize naturally and reuse final output storage. Large browser scalar
head/threshold/discount/spread-total wins do not generalize to every cell;
dead-fold and vector spread still lose to their Rust controls on that fixture.
Expert direct-head/ignored-input or already-factored handwritten controls are
unmeasured, and wrapper/transport contracts differ. No language ranking follows.

Final review passes with retained adverse results, the borderline GPU interval,
mixed-bundle restriction and original-control limitations. Validity, executable
application, shader eligibility and measured profitability remain separate.
Wasm memory observations are exported linear-memory highwater only; host/GPU
memory is unmeasured. Previous archived receipts remain unchanged.

## Supplemental JavaScript selection: unsuccessful performance repair

The separate locally checked compile-time selection retains six scalar law
applications and drops the scalar spread-factor application inside spread-map.
Actual archived core comparison confirms that its spread-map body equals the
original body and each of its six scalar bodies equals unrestricted checked
output. The selected core hash is
`978958b1d2b771e2a66551d2bc38985909f854d8c2e2d2c43540871e73812311`;
the source core, proof snapshot and frozen compiler remain unchanged. The
check-selection, reification and build receipts all succeed. This is a
source-specific compilation candidate informed by the measured matrix, not
an automatic profitability policy or a new proof batch.

Independent post-measurement inspection passes all 59 supplemental hashes and
all 72 original main hashes. The 18 copied prior/checked bundle artifacts are
byte-identical to their original main artifacts. Node and browser each archive
2,058 trials, 294 warmup rows, 294 calibration rows and 931 exact comparisons.
The seven JS-only variants cover all 42 cells with seven unique paired rounds.
All phases pass independent checksum and per-call normalization checks; every
summary median equals its raw median. Actual availability is JavaScript, with
no GPU samples/counters or memory observations. The supplied audit implements
the same shared-round bootstrap and 252 intervals per host. The supplemental
server uses its dedicated root and absolute result POST; frozen raw scope
correctly declares JS-only execution and `webgpu:false`.

The candidate retains 72 supported scalar gains per host across runtime/direct
JS, but spread-map still regresses in all 12 comparisons per host. Full65536
prior/gated runtime ratios are Node 0.59954 [0.52762,0.77251] and browser
0.75727 [0.70663,0.80096]. Direct ratios are Node 0.55982 [0.53653,0.63167]
and browser 0.80112 [0.71713,0.82973]. All four unrestricted/gated comparisons
on that fixture are inconclusive. Restoring the original expression therefore
fails to establish restored performance; this candidate cannot be presented
as a no-regression replacement for the prior artifact.

Read-only emitted-code inspection verifies the restored two-imul/subtract
expression, with only generated identifier differences from the prior vector
function. The surrounding modules differ: prior uses the shared `__map` helper
from seven functions; gated uses it only from spread-map and removes the
ignored-fold helper. Runtime wrappers and backend-selection bytes are unchanged
between prior and gated. Helper/callsite feedback, module context and JIT
optimization are plausible confounds, but no cause is established without
controlled follow-up. Direct JS's same adverse pattern means runtime wrappers
alone cannot explain the result. The earlier inside-callback factor expression
is not an established sole cause either.

Retain the previously measured prior vector artifact for these profiles; the
rebuilt six-law bundle is not evidence that candidate-level law removal alone
restores prior latency. These are same-workload follow-up profiles, not a
generalization study or holdout evaluation. Both the successful scalar results
and unsuccessful vector repair remain archived. Total main plus supplemental
measurements are 10,710 samples and 4,914 exact backend comparisons, with the
91 JS preflight and 124 literal Python checks reported separately.

The combined report's performance counts, scope, unsuccessful-candidate
qualification, GPU restrictions, original Rust control limitations and mixed
CPU routing claims agree with this review. The derived profitability scope
now correctly names old809; the frozen inherited old786 label is disclosed.
