# Independent review of web proof batch 4

The immutable baseline is the 786-member snapshot
`f5ef7bfd79adee16ef47984bd149811cc66dfe7b936820fbd2b68eb0e4170ab9`.
The frozen compiler remains SHA256
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
This lane writes only this new review; previous hashed receipts are unchanged.
No compiler, proof-search, build, test or timed workloads run in this lane.

## Discovery

Existing catalogue families already include map/count, mapped filter/count,
filter/map/sum, ordinary map fusion, same-source mapped zip, ordered folds and
captured recurrence laws. Names include research definitions and aliases outside
the executable membership set, so a new name is not evidence of a new useful
rewrite. Every retained candidate needs endpoint novelty, an immutable old786
control leaving the actual source unchanged, and a fresh default-planner
application checked and reified by the frozen compiler.

The reviewer suggested mapped first-element lookup:
`xs.map(f).at_or(0,f(z)) = f(xs.at_or(0,z))`. It removes a full map for a common
head read and handles empty input by mapping the fallback. Concrete arithmetic
callbacks can avoid generic application reification limits. The constant-zero
index fits the current finite-list definitional equations; a dynamic index is a
separate induction problem. This is a proposal, not an admitted or measured law.

Captured invariant branch movement may remove repeated decisions, but ordinary
backend optimizers may already hoist them. Generic multiplication recurrences
need appropriate geometric-series semantics or conditions, rather than an
unjustified linear closed form. F32 rewrites must retain exact arithmetic order
and bit semantics. No higher-degree polynomial family is proposed.

## Collection source and proof review

The final collection producer has twelve laws: generic unary maps on the left,
right or both sides of a same-source zip, with concrete combiner `x-y*k`, for
U32/I32/U64/F32. Every mapped input preserves the original length, so zip
truncation equals the single target map's length, including empty input. The
target substitutes each pure unary callback once per element into the original
subtraction/multiplication expression. Exact operand order and F32 arithmetic
grouping remain unchanged. Global invocation scheduling changes: full-list maps
followed by zip become interleaved operations per element, which the pure value
semantics permit. This is not equality of allocation, failure or resource cost.

The initial fully generic curried zip callback was admitted mathematically, but
the current executable reifier rejected nested callback applications. The author
retained that failed experiment and narrowed the concrete combiner, rather than
changing the trusted checker or publishing an unusable rule. Generic unary
callbacks remain in the final laws. The reviewer read the final three passing
author tests and assertions: all twelve admitted, no duplicate IDs or endpoints
against pinned786, old bodies unchanged with zero applications, every fresh
default selection replayed and reified, and two valid-hash false controls rejected
for differing semantic normal forms. The false controls duplicate a mapped
argument or swap F32 callback operands; rejection is not merely a hash mismatch.
No reviewer test/compiler jobs were run.

## Compute and benchmark source review

The final compute producer contributes eleven laws: weighted-difference
same-source zip and zip-then-unary-map for U32/I32/U64/F32, plus scalar
`x*k+(d-x)*k = d*k` for the three wrapping word types. The zip combiner is
concrete `a-b*k`, avoiding the failed generic curried reification path while
retaining a generic pure unary post-map callback. Finite-list induction preserves
count and exact per-element grouping. Scalar conservation uses the wrapping
word ring and explicitly excludes F32; no range assumptions are required.

The reviewer read the six passing compute author tests and durable evidence:
all eleven objects admit, default selections replay and reify across all four
applicable types, endpoints/IDs are fresh against786, and three fresh-hash false
controls reject semantically. Original and selected interpreter fixtures cover
empty/singleton and word overflow for U32/I32/U64, finite F32 rounding and signed
zero, with original/selected bit equality also checked for infinities and NaN.
The F32 special-value comparison checks equality to the original interpreter,
not an independently specified NaN payload implementation. The old786 U32 core
is unchanged at SHA256
`142bbf917a19bf482f53d4e147085fddf5bc871211829f06ace5f74a1feaa981`;
the author's union797 selects three fresh laws, one per function. Every recorded
compute artifact hash matches at read-only review time.

All six benchmark sources match the handwritten JS/Rust source stages and
independent Python modular result oracles. Original collection controls retain
materialized maps/zips; the self-zip/post-map and conservation controls retain
their original operations. Python literal evaluation wraps every operation,
whereas the oracle uses arbitrary integers and reduces once per final word.
The archived preflight reports 78 full handwritten-JS comparisons and 276 literal
Python checks. Rust source intermediates use ordinary Vec/release optimization,
and its final destination is preallocated/reused. An expert already-fused or
algebraically simplified handwritten control is unmeasured.

The shared driver pays one typed-input snapshot per implementation, applicable
Wasm copies and result conversion, awaited boundaries and checksum consumption
inside the warm timer. Exact per-element output validation and original-input
nonmutation run before timing. Startup and first calls remain separate. Actual
GPU timing requires one dispatch, `4*N+24` upload bytes and `4*N` readback bytes
per call, with trial/calibration/warmup aggregates retained for independent audit.
Fallbacks never enter GPU samples. The summarizer only emits same-backend GPU
ratios when both variants actually execute shaders and now also emits current
checked CPU/GPU comparisons. Mathematical admission, executable applicability,
shader eligibility and measured route profitability remain distinct.

## Frozen artifacts and completed measurements

Frozen preparation inspection passes: all 79 archived hashes match, including
the unchanged compiler/methodology identities and current/frozen controls. The
809-member catalogue is snapshot
`388e3ebd2714c88bc66ae9219102284162f4f65cbed359283f54896b3cfac87c`.
Prior selection has zero applications and original/selected core SHA256
`9d114d25ba3efceb94c26c8b1fa7a51c9379f1daa6171854f35e11f8e220d06c`.
Checked SHA256 is
`86dcc9318051e7beebfed4b9c168a51579c25ea59aa01657a29f9475da1a41bc`,
with six fresh applications changing every function body. The reviewer compared
archived bodies independently. CPU validation passed. All six checked functions
have shaders; original/prior self-zip and conserved-total have shaders, while the
four other original/prior shapes retain explicit fallback reasons.

Post-measurement inspection also finds no hash discrepancy. Node archives 2,772
timed samples and 1,254 exact comparisons; the browser archives 3,192 samples and
1,362 comparisons, for 5,964 timed samples total. Both hosts have 36 workload
cells and 144 measured Wasm observations. The six U32 representatives use small/
full-width distributions and sizes 32/4096/65536. These measurements do not
profile all 23 typed law instances. Hardware remains Apple M2, with headed
Chrome 154/Apple Metal-3 for actual WebGPU calls.

Independent raw inspection verifies every saved trial, warmup and calibration
checksum and per-call normalization, every GPU counter aggregate, availability
counter and fallback classification, and summary medians against raw trials.
No mismatch is found. Browser timing contains 60 actual GPU variant/cells and
420 timed GPU rows; calibration and warmup each contain 60 GPU rows. The 48
original/prior GPU-request fallbacks for three mapped zip functions and
zip-then-map do not enter GPU timing. No prior/new GPU ratio is invented for
these newly eligible functions. Root separately regenerated all 816 saved paired
intervals exactly. Reviewer checks did not recompute bootstrap intervals, run
compiler/test jobs or create new timings.

Same-backend prior/new classifications agree with the profitability receipt:
147 supported improvements, 80 inconclusive and one supported regression among
228 comparisons. Node runtime JS has 35 wins/1 inconclusive, Wasm 5 wins/
30 inconclusive/1 regression, and direct JS 36 wins. Browser runtime JS has
35 wins/1 inconclusive, Wasm 1 win/35 inconclusive, direct JS 34 wins/
2 inconclusive, and comparable actual GPU calls 1 win/11 inconclusive. Individual
95% intervals remain exploratory and unadjusted for the many comparisons.

The original Node `generic_both_zip` full65536 Wasm prior/new ratio is
0.99254 [0.97247,0.99937]. Its small supported regression must remain in the
record even if a separate unchanged-artifact confirmation is inconclusive or
shows a different sample outcome. The completed separate full Node protocol
repeat has focus ratio 1.03241 [0.98388,1.04655], inconclusive: the original
adverse observation was not reproduced, but non-regression is not established.
The original trials and interval remain immutable and are not pooled with the
repeat. All other original same-backend adverse medians have intervals crossing
1 and do not establish a regression.

The reviewer independently checks identical original/confirmation 79-artifact
hash maps and actual bytes, identical parameters, all 2,772 repeat trial,
396 warmup and 396 calibration checksums/normalizations, and raw/summary medians.
No discrepancy or unexpected GPU timing/counter is found in this Node repeat.
Root independently regenerates its 324 intervals. Its separate classifications
are 74 supported improvements, 33 inconclusive and one adverse interval: a
different borderline Wasm comparison, `generic_right_zip` small65536,
0.997837 [0.990104,0.999990]. This repeat is not wholly regression-free; the
individual unadjusted intervals and differing near-unity outcomes limit firm
profitability claims about these small Wasm effects.

At browser full65536, runtime JS improves by 1.562/1.580/1.901 for the three
generic mapped zip functions, 1.200 for self-zip, 1.477 for zip-then-map and 1.296
for conserved-total, each interval above 1. The corresponding large Wasm
intervals all cross 1. Large comparable GPU results are likewise inconclusive:
self-zip 0.9704 [0.9364,1.0556] and conserved-total
0.9766 [0.9500,1.0043]. The sole supported same-backend GPU gain is conserved-total
at small32, 1.0912 [1.0523,1.1821]. Legal and checked GPU output therefore does
not imply broad GPU speedups from these laws.

The current-backend routing receipt matches saved summary medians and intervals
for 36 unique browser cells. Current checked runtime JS has the lowest median
in all 36; both checked CPU routes beat checked GPU in all 72 paired comparisons
(maximum interval upper bound about 0.7853). GPU eligibility gains are real, but
these complete-call contracts favour CPU execution on the measured matrix.
This is a scoped measured recommendation, not an implemented automatic routing
policy or a prediction for GPU-resident/fused pipelines.

Against original-algorithm controls, direct generated JS wins all 36 cells per
host. Runtime JS wins 34 cells per host; Node loses the two self-zip length32
comparisons, while those browser comparisons are inconclusive. Checked Ink/Wasm
loses to original Rust-Wasm in all 36 cells on each host; at full65536 the browser
ratios are about 1.65–1.69. Rust release/library optimization may remove original
arithmetic or allocations naturally, and its final destination is preallocated/
reused. The original ordinary-array JS controls retain materialized source stages.
An expert already-fused or algebraically simplified handwritten control is
unmeasured, and wrapper/transport contracts differ. These measurements establish
no general language ranking.

Final review passes with the recorded regression, inconclusive intervals,
control-style and GPU-route limitations. Correct proofs, executable applicability,
shader eligibility and measured profitability remain separate conclusions. Wasm
memory observations measure exported linear-memory highwater only; host/GPU
memory is unmeasured.
