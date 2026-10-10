# Independent review: web proof batch 7

Read-only discovery and review lane; only this new review file is writable.
Existing proof objects, source changes, canonical publication and previous
measurement archives remain outside this lane. No compiler/test/timing jobs
are run by this reviewer without coordination.

Baseline is the immutable 854-entry snapshot
`97f7f5263af8e184c1b68559220e0182f3beda7802fe0b4ea372faac5d898044`.
Frozen compiler SHA256 is
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
Freshness requires old854 to leave the actual representative sources unchanged,
not only new catalogue names or object identities.

## Indexed semantics and discovery

Indexed map unfolds to `indexed.from(xs,Nat0,f)`. Cons applies the curried
index-first callback to `nat.word(index):U32` and the element, then advances the
mathematical Nat index for the tail. Therefore the visible callback index wraps
modulo 2^32; there is no new caller length guard or index saturation policy.
Fusion proofs involving index use should generalize the internal start index
before list induction. A tail `map_indexed` restarts at zero and is not the
same induction hypothesis as a shifted traversal. JS/C/GPU lowering preserves
index-first callback order and the typed U32 index for supported arrays.

GPU-v2 accepts direct input-rooted map/indexed-map/zip; nested collection receivers
fall back. Indexed pipeline fusion may therefore establish eligibility without
establishing a prior/new GPU improvement. Static scalar algebra inside direct
maps may provide both shader sides, but arithmetic removed from source may
already be simplified downstream. Old weighted-add factoring and batch5 spread
factoring are existing laws; they are not new contributions for this batch.

Batch5/6 results show that simple factoring and self-zip-to-map changes can
regress JavaScript, and restoring an old expression in a rebuilt module need
not restore latency. No assumed benefit follows from fewer operations. Retain
all adverse/inconclusive results and distinguish proof correctness, executable
applicability, shader eligibility and complete-call profitability.

## Final producer and harness source review

Compute contributes nine static word identities: centered energy
`x*x+d*d-2*x*d = (x-d)*(x-d)`, complementary interpolation
`x*k+(x+d)*(1-k) = x+d*(1-k)` and calibrated energy
`(x*d)*(x*d)+2*(x*d)*k+k*k = (x*d+k)*(x*d+k)` across U32/I32/U64.
These are exact wrapping-ring identities checked by existing Normalize, with
explicit source association and no F32 reassociation or artificial loops.
Supplied author receipts show six tests pass in 7.628 seconds, old854 unchanged,
default matching/replay/reification for all three types, 36 original/selected
interpreter frames and 5,472 independent literal/oracle scalar cases. Three
valid-hash false targets reject for semantic mismatch. The twelve archived
compute evidence hashes pass independent inspection; no tests are rerun here.

The final collection producer contains twelve selecting self-zip/postmap laws,
rather than indexed fusion. Minimum and maximum selectors over the same source
list return the same element on either branch, then fuse the arbitrary pure
unary postmap. Equality routing fuses the same-list zip but retains `x==x` in
the target: this is essential for F32 NaN, where the false branch remains
observable. All four numeric types are included, with operation grouping and
F32 seed/payload semantics retained. Indexed semantics were inspected only as
discovery; no indexed candidate/proof execution or rejected run is claimed.

Six U32 harness sources are centered-energy, complementary-blend,
calibrated-energy, minimum-route, maximum-route and equality-route. Original
JS/Rust/Python controls preserve the original arithmetic grouping and wrap each
operation. Route controls retain the intermediate selecting zip followed by a
separate map. Python output oracles use unbounded integer closed forms reduced
at the final output, independently of source-stage wrapped evaluators. Both
minimum/equality U32 oracles reduce to `x*k+seed`, while maximum retains the
original `x<seed` decision. Root reports 78 original-JS outputs and 276 ordered
Python stage checks; complete backend validation still remains separate.

The three static maps have direct GPU source shapes on both sides. The route
sources have nested collection receivers and may only gain eligibility after
selection; this cannot be described as prior/new GPU acceleration when prior
falls back. Caller-list aliasing inside self-zip requires only one input capture
and upload. All paths retain O(N) output writes/transport/consumption, and Rust
reuses final output storage while ordinary release optimization remains allowed.
No source/control/oracle blocker is found in the adapted harness.

The final collection three-test log passes in 14.935 seconds, covering twelve
fresh statements, old854 unchanged controls, admission/default selection/replay/
reification and two valid-hash false endpoint controls. Combined publication
therefore adds 21 mathematical laws; no indexed law is claimed.
The archived collection interpreter results cover 39 complete-array frames,
including exact F32Bits signed zero, NaN and positive/negative infinity. Equality
oracle uses the false branch's seed factor for NaN, and compares exact output
bits. This independently exercises the predicate retained in the F32 theorem.

## Frozen preparation

Independent read-only inspection passes 82 pinned artifact hashes, 102 guarded
core/runtime/planner/lowering source hashes and frozen compiler/methodology
identities. Nine active/frozen source/control/protocol files are byte-identical.
The 875-entry snapshot is
`7236d0bffbe86aa0fac98bd47c12d2345b864043cb7bde3a8a7b67b3ee27d1ca`.
Actual archived original/prior functions are equal, with zero prior law
applications. Six fresh default-selected applications change all six bodies;
actual selected expressions agree with the independently reviewed oracles.

Metadata confirms three original/prior shaders and six checked shaders. Only
the static arithmetic functions support prior/new GPU comparisons. All three
route cases have the input-root requirement fallback before selection and
become eligible afterward. Shader metadata is not evidence of dispatch or a
profitable route; actual complete-call counters and measured intervals remain
required.

## Completed measurements

The full knowledge suite passes 76 tests in 124.239 seconds; root CPU
prevalidation passes 858 comparisons. Final post-measurement hashing again
passes all 82 frozen artifacts, 102 guarded source files and compiler/
methodology identities. No timed/compiler/test jobs run in this lane.

Node archives 2,772 trials and 1,254 exact comparisons; browser archives 3,276
trials and 1,362 comparisons, totaling 6,048 trials and 2,616 comparisons.
Independent raw checks pass every trial, warmup and calibration checksum,
per-call normalization, unique round and summary/raw median. Node warmup and
calibration each contain 396 rows, browser each 468. Browser records 72 actual
GPU variant/cells, 504 GPU trials and 72 GPU rows in each warmup/calibration
phase. Every GPU row and availability record has the expected dispatch/upload/
readback counter totals. The 36 original/prior route fallbacks remain excluded
from GPU timing. Root's independent receipt recomputes all 828 paired intervals
exactly; shader eligibility and actual execution are distinguished correctly.

Same-backend comparisons classify 138 supported gains, 94 inconclusive and two
supported regressions across 234 comparisons. Node runtime JS has 34 gains/
2 inconclusive, direct JS 33/3 and Wasm 4/32. Browser runtime JS has 32/4,
direct JS 34/2, Wasm 1 gain/34 inconclusive/1 regression and comparable GPU
17 inconclusive/1 regression. The adverse browser cells are complementary-blend
small65536 GPU, prior/new 0.98710 [0.97436,0.99355], and centered-energy full32
Wasm, 0.98941 [0.93287,0.99696]. Both remain material and archived. These
individual exploratory 95% intervals are unadjusted for many comparisons.

All six full-width65536 runtime/direct JS comparisons improve on both hosts.
Browser runtime ratios are centered-energy 1.19314 [1.17037,1.26651],
complementary-blend 1.25800 [1.21073,1.29975], calibrated-energy 1.24260
[1.19283,1.29102], minimum-route 1.20938 [1.17836,1.24124], maximum-route
1.05263 [1.03205,1.05960] and equality-route 1.09397 [1.07283,1.11556].
Corresponding Node medians range 1.04294–1.72130. These are static arithmetic
and selecting self-zip stage improvements, without synthetic repeat counts.
Timing covers six U32 representatives, not all 21 typed theorem instances.

All full-width65536 Wasm intervals include one, as do all three comparable
static-map GPU intervals. There is no supported GPU speedup in this batch,
and a supported smaller-input GPU regression. Three route cases become GPU
eligible after selection but have no prior/new GPU ratio. Current checked JS
has the lowest median in all 36 browser cells; all 72 current CPU/GPU paired
intervals favor CPU, with maximum upper ratio bound 0.81349. Eligibility or
an arithmetic simplification does not establish a profitable GPU route for
these complete-call contracts. GPU-resident/fused pipelines and larger workloads
remain unmeasured; no automatic routing policy is implemented.

Against original handwritten JS, checked direct JS has supported gains in all
36 cells per host. Runtime JS has 35 gains/1 loss in Node and 35 gains/
1 inconclusive in browser. Checked Wasm loses to original Rust-Wasm in all
36 cells on each host. Rust retains original operations and stages while normal
release optimization and final output-storage reuse remain allowed; expert
already-fused/simplified controls and equal boundary implementations are not
measured. These results do not rank languages generally.

Uncompressed emitted JS shrinks 3,588→3,171 bytes and C 10,088→8,981. Wasm
instead grows 21,599→21,788 bytes, by 189 bytes; output size does not uniformly
shrink. Shader count changes three→six, so aggregate shader bytes are not a
like-for-like size comparison. Runtime/proof-plan/compressed transfer costs are
excluded. The import receipt records 288 authenticated Wasm observations,
3,870→4,158 total, while preserving the 875-entry proof snapshot. Exported
Wasm linear-memory highwater is the only canonical memory metric; host/GPU/JS
memory is unmeasured and no values are fabricated.

Final review passes with retained regressions/inconclusive cases, no GPU-win
claim, explicit selecting-self-zip scope and original-control limitations.
Previous archives remain unchanged.
