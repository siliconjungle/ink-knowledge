# Independent review: web proof batch 6

Read-only discovery/review lane. Only this new review is writable; previous
proof, benchmark and adverse-result archives remain unchanged. No compiler,
validator, backend or canonical-store changes are part of this lane.

## Discovery and scope

Baseline is the immutable 834-entry snapshot
`2e4106786af6f3cd41dbad39438c52dd9d518397b7a69b2841a525959c994f34` with
compiler SHA256
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
The existing catalogue already contains same-type map fusion, cross-type map
fusion, self-zip conversion, weighted arithmetic and several concrete mapped
zip families. Fresh names alone do not establish additional applicability;
the old default planner must preserve each representative source body.

Current GPU-v2 lowering requires direct input-rooted map/map_indexed/zip output.
Mapped receivers, filters and scans fall back. Fusion may establish eligibility
without establishing a GPU-to-GPU latency improvement. Both original/prior and
checked shaders, actual dispatch records and complete-call costs are required
for that comparison. Legacy-v1 scalar pipelines have a different stage contract
and must not be inferred from mixed-v2 fallback observations.

Suggested fresh candidates to the authors are direct complementary word blend
`x*k+(x+d)*(1-k) = x+d*(1-k)` and centered-square word evaluation
`x*x+k*k-2*x*k = (x-k)*(x-k)`. These reduce per-element arithmetic while preserving
fixed-size vector outputs, without introducing higher-degree recurrences.
They are suggestions pending proof admission, executable selection and old834
controls, not checked additions or profitability claims. F32 reassociation is
excluded from these word-ring suggestions. Existing repeat-specific affine
blend laws do not by themselves establish selection of the direct-map pattern.

Batch5 demonstrated that a valid arithmetic rewrite, and even restoring the
original vector expression in a rebuilt module, can regress JavaScript. Module
and helper/JIT context remain plausible confounds with no established cause.
Batch6 must retain all adverse results and distinguish proof correctness,
executable applicability, shader eligibility and measured profitability.

## Final producer and control review

The actual compute lane contains nine wrapping-word recurrence laws, rather
than the optional direct-arithmetic suggestions above. Complementary captured
contributions have step `a+d*k`; captured conditional weighting has step
`a+offset*(1-selected_weight)`; the compensating update has step `a`.
All endpoints are valid modulo the declared word width. The condition is a
captured Bool, not recomputed from the evolving accumulator. Cases/Trans followed
by general Nat induction use the existing checker, with no new trusted rule.
The measured instances explicitly use 64 synthetic steps and outer `+seed`.
No real application iteration count or general workload benefit is implied.

The collection lane contains eleven laws: square self-zip and square self-zip
followed by an arbitrary pure unary postmap, across U32/I32/U64/F32, plus
self-squared-distance elimination across the three wrapping word types.
Self-zip length/order semantics make the square/map identities exact. F32
square/postmap preserves the original operation order; F32 distance-to-zero is
correctly excluded because subtraction of an exceptional value from itself
need not produce zero. The generic unary postmap target is reified successfully
in the final source fixtures rather than relying on an unsupported curried
application pattern.

Read-only author receipts show collection admission/default selection/replay/
reification, old834 unchanged controls, eleven fresh statements and 33 full-array
original/selected interpreter frames. Its three tests pass in 13.492 seconds;
two valid-hash wrong-product/nonzero-distance controls reject semantically.
Compute's six-test log passes in 8.817 seconds, covering nine fresh statements,
all word types, old834 unchanged/default new selection, replay/reification,
zero/one/64-count interpreter checks and independent wrapping recurrence checks
at zero/one/two/17/64 counts. Both captured branch sides and word boundaries are
covered; three valid-hash false recurrence controls reject semantically.
These are supplied execution receipts, not tests rerun by this review lane.

The final six U32 source/control functions are contribution-repeat,
conditional-blend, compensated-patch, squared-values, calibrated-squares and
self-squared-distance. JS and Rust handwritten controls use independent loops
for each recurrence, preserving captured original-input decisions and wrapping
after each operation. Collection controls retain original zip/map stages;
calibrated Rust squares materializes its intermediate Vec, with ordinary release
optimization allowed. Rust output storage is preallocated/reused. Python literal
stages are distinct from the arbitrary-integer closed-form output oracle.
Empty/singleton/extreme words and zero/unit factors are included; every backend
output element and original input nonmutation are checked before timing.

An initial copied-source naming mismatch was reported before preparation and
fixed: final kernel names now agree with harness CASES, runner and JS controls.
Root reports 78 complete JS preflight outputs and 276 independent ordered Python
checks. No pre-freeze control/oracle blocker remains.

Every measured implementation pays one full input snapshot, applicable Wasm
copy/output conversion, awaited completion and checksum consumption. Self-zip
uses the same single caller list twice, so it does not imply two caller snapshots
or two distinct input uploads. GPU per-call gates require dispatch 1, upload
`4*N+24`, readback `4*N` and the actual requested backend. Calibrated-squares has
a nested original pipeline and may become eligible only after selection; it
cannot establish a GPU-to-GPU gain if the prior route falls back. Direct zip
square and self-distance may already receive driver simplification. All vector
outputs still require O(N) writes, transport and consumption.

## Frozen preparation

Independent read-only inspection passes all 86 pinned artifact hashes plus the
frozen compiler and methodology hashes. Nine active/frozen source, control and
protocol files are byte-identical. The extended 854-entry snapshot is
`97f7f5263af8e184c1b68559220e0182f3beda7802fe0b4ea372faac5d898044`.
Actual archived original/prior function objects are equal, with zero prior
applications. Six fresh checked applications change all six bodies; selected
core expressions agree with the independently reviewed closed-form oracles.
All original/prior and checked bundles retain fixed-size U32 array outputs.

Metadata confirms five shaders for original/prior and six for checked.
Calibrated-squares alone is an eligibility transition, with original/prior
fallback reason requiring an input-rooted GPU source. The other five workloads
have both shader sides available for subsequent actual-backend measurements.
Metadata establishes eligibility only; dispatch counters and final latency
observations must still establish execution and profitability.

The supplied source-boundary receipt separately pins 102 core, runtime, planner
and lowering files. Independent read-only hashing confirms every guarded file
is unchanged before timing. Root reports CPU validation passes 858 complete
backend comparisons; five total false controls comprise three compute and two
collection counterexamples.

## Completed main measurements

The final full knowledge suite passes 67 tests. Compute author evidence pins
twelve archived files, all independently hash-checked; its producer remains
SHA256 `2fad5ba3af1f963fed69499f083aebe94a0aee63dd7a081da00cf846a833a018`.
Post-measurement inspection again passes all 86 frozen artifact hashes, the
compiler/methodology identities and all 102 guarded source hashes. No timed,
compiler or test jobs run in this review lane.

Node records 2,772 trials and 1,254 exact comparisons; browser records 3,444
trials and 1,362 comparisons, for 6,216 main trials and 2,616 comparisons.
Independent raw checks cover every trial, warmup and calibration checksum,
per-call normalization, unique round and raw/summary median. Node warmup and
calibration each have 396 rows; browser each has 492. Browser has 96 actual GPU
variant/cells, 672 GPU trials, and 96 GPU rows in each warmup/calibration phase.
The twelve original/prior calibrated-square fallback records are excluded from
GPU timing. Every actual GPU availability and aggregate row has the expected
dispatch/upload/readback totals. Availability additionally records live-buffer
bytes; these are not whole-process memory observations. Root's independent
receipt recomputes all 852 paired intervals exactly.

Main same-backend classifications are 115 supported gains, 110 inconclusive and
21 supported regressions across 246 comparisons. Node runtime JS has 26 gains/
5 inconclusive/5 regressions; direct JS 25/7/4; Wasm 7/29/0. Browser runtime JS
has 24/7/5, direct JS 24/6/6, Wasm 7/28/1 and comparable GPU 2/28/0.
All nine Node regressions are squared-values in runtime/direct JS. Browser
regressions comprise seven squared-values JS/direct comparisons, four
self-squared-distance JS/direct comparisons and compensated-patch small32 Wasm.
These adverse results remain material even though all selected proofs are valid.
No operation-count reduction establishes latency profitability.

The two main supported GPU improvements are conditional-blend at small65536
1.02516 [1.01887,1.05844] and full65536 1.01829 [1.01212,1.03636]. These are
modest complete-call gains on synthetic captured-branch 64-step word models.
Contribution-repeat full65536 has prior/new 1.06098 [1,1.07407], which includes
one and is unresolved despite its original-source/new interval excluding one.
Calibrated-squares is only an eligibility transition and has no prior/new GPU
ratio. The other comparable GPU intervals do not establish differences.

Current checked runtime JS has the lowest median in all 36 browser cells. All
72 checked CPU/GPU paired intervals favor CPU, with maximum upper ratio bound
0.79268. Thus a small GPU-to-GPU improvement does not establish that GPU is the
profitable route for these complete calls. GPU-resident/fused pipelines and
larger workloads are unmeasured; no automatic routing policy is implemented.

Original handwritten controls preserve ordered source stages and allow normal
JIT/release optimization. Per-operation wrapped recurrences are independently
written, while Rust reuses input/output destinations and may eliminate or
vectorize redundant work. Checked runtime JS versus original JS is 31 gains/
4 losses/1 inconclusive on each host; direct JS is Node 32/1/3 and browser
31/1/4. Checked Wasm versus original Rust-Wasm is six gains/thirty losses on
each host. These comparisons do not rank languages or an expert already-closed-
form implementation. Full-call capture, copying/conversion, output allocation
style and checksum costs remain part of the stated contracts.

## Separate focused GPU confirmation

Before confirmation, independent inspection passes all 86 confirmation hashes
and confirms 84 copied payloads are byte-identical to the main artifacts. Only
the timed-cell list and browser label differ. All fixture inputs, expected
outputs, source cases, compiler and protocol parameters are unchanged. Four
cells repeat contribution-repeat/conditional-blend at small/full65536; this is
a focused same-workload confirmation, not an independent workload generalization
study. Original results remain immutable and the samples are not pooled.

Independent final raw checks pass 392 trials, 56 warmups, 56 calibration rows,
914 exact comparisons and all summary medians/normalizations/checksums. Twelve
actual GPU variant/cells produce 84 trials and twelve rows in each warmup/
calibration phase, with correct counter aggregates and no fallbacks. Sixteen
Wasm observations are saved. The supplied independent interval receipt covers
60 paired intervals. Same-backend classification is fourteen nominal gains and
two inconclusive comparisons, kept separate from the main classification.

Full65536 conditional-blend prior/new GPU is 1.04819 [1.01205,1.07975], supporting
the modest main benefit on this fixture. Full65536 contribution-repeat is
1.03727 [1.01863,1.06289] in the repeat, while the original interval remains
unresolved. Small contribution-repeat remains inconclusive. Small conditional-
blend nominally passes the strict classifier, but its lower bound
1.0000000001186 is effectively one; it is borderline evidence, not a broadly
corroborated gain. Individual intervals remain exploratory and unadjusted for
the many comparisons. CPU route profitability and original-control limitations
remain unchanged by this focused evidence.

Main plus confirmation total 6,608 trials and 3,530 exact backend comparisons.
The main matrices save 288 authenticated Wasm observations and confirmation
saves sixteen, for 304 total. Proof coverage is twenty typed mathematical laws;
timing coverage is six U32 representatives. Host/GPU memory is unmeasured;
exported Wasm linear-memory highwater is the only canonical memory metric.

Final review passes with all adverse/unresolved cases retained, explicit
synthetic-model labeling, separate confirmation evidence, calibrated-square
eligibility scope and CPU routing limitations. Previous archives are unchanged.
