# Independent review of web proof batch 3

The immutable baseline is the 765-member snapshot
`7ecbce6e14b1273e771e4634b61e92d0f85929934c0d4e165b1f14c7c8660c6c`.
The frozen compiler remains SHA256
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`.
This reviewer writes only this new review. Previous hashed receipts are
unchanged; no compiler, tests, proof search or timed jobs run in this lane.

## Discovery and source review

The existing catalogue already covers repeat arithmetic/invariants,
quadratic-through-quintic finite differences, map fusion, fixed same-source
zip operations, ordered map/filter folds and concat composition. This batch
should prefer common composition/branch patterns rather than additional
polynomial degrees or renamed statements. Every retained source must have an
old-765 control and real new default selection/replay/reification.

The reviewer suggested mapped first-element lookup as a later useful family:
`xs.map(f).at_or(0,f(z)) = f(xs.at_or(0,z))`. It removes a full map, handles
empty lists with a mapped fallback, and avoids the current dynamic-index proof
limitations. It is not part of the selected collection batch. General scalar
branch factoring can similarly expose a loop-invariant increment to the already
checked repeat-add law, avoiding unsupported special optimization rules.

The final `web_collection3_laws.py` source defines twelve same-source mapped zip
laws: mapped-left addition, mapped-right subtraction and both-mapped subtraction
for U32/I32/U64/F32. Both source lists derive from the same input, so their
lengths coincide and zip truncation equals one map's length, including empty
inputs. Targets retain element order and exact multiplication/addition/subtraction
grouping. F32 operands are not factored or reversed; scheduling changes only
the order of independent pure element operations. Author receipts show three
passing tests, all twelve admitted/selected/replayed/reified, old-765 bodies
unchanged, and semantic rejection of hash-valid wrong-operator and reversed
F32 subtraction controls. The reviewer has not rerun those tests.

Mapped zips may be GPU-ineligible before rewriting and GPU-eligible as direct
maps afterwards. A new GPU execution is useful eligibility evidence, but it
cannot establish a speedup between two GPU shaders when the prior source used
CPU fallback. Actual backend, shader availability and complete dispatch/transfer
counters must be recorded per variant. The three batch-2 scalar fallback
results must not be relabeled as GPU evidence for this batch.

## Numeric laws and harness source

The final compute producer contains nine word-only instances: fixed captured
branch recurrence, complementary affine blend and initialized projection, each
for U32/I32/U64. The branch condition is a captured Bool independent of the
changing accumulator. Cases reduce the recurrence to the corresponding plain
addition/subtraction branch, and transitivity plus natural induction establish
the closed forms. The affine update is
`a*k + (a+d)*(1-k) = a + d*(1-k)` in the wrapping word ring; it makes no F32
reassociation claim. The projection starts at `choose(c,k,x)`, so even zero
iterations equal its target. The proof uses existing general Cases, Trans,
Induction and Normalize mechanisms without kernel changes.

The reviewer inspected the six source functions and original-algorithm JS/Rust
controls. Mapped zip controls materialize the original map stages and retain
ordered zip truncation. Numeric controls retain 256 original updates, fixed
original-input conditions and per-operation word wrapping. Rust normal release
optimization can remove such loops naturally; its reused preallocated final
destination is explicitly disclosed. Expert already-fused or closed-form
handwritten alternatives are not included.

Independent Python arbitrary-integer modular closed forms match the source
algebra. A separate literal Python evaluator reduces every original operation
and corroborates all boundary elements and the first four elements of each
remaining vector fixture. The archived control preflight records 78 comparisons,
276 literal checks and 13 fixtures, including empty/singleton, full-width words,
zero multiplier and none/all captured-condition branches. No reviewer jobs
were run. The stale 18-versus-9 uniqueness assertion was corrected, with its
failed log retained separately. The final numeric receipt records six passing
tests: all nine admitted/selected/replayed/reified, no duplicate statements or
IDs against old765, independent literal boundary checks and actual original/
selected interpreter outputs for all three word types at counts 0/1/256.
Three hash-valid false recurrence controls fail for different semantic normal
forms. The compute author control records zero old765 applications and identical
input/selected core SHA256
`9dd610996feae35928d028a018ae6090c44d490ea71252646f2a3b3078cef97d`;
its union774 makes exactly three fresh applications, one per U32 function.

The shared runner includes a typed input snapshot, transport, result conversion,
awaited calls and checksum consumption inside its timer. Exact per-element
validation and original input nonmutation checks run before timing. GPU timing
requires actual backend `gpu`, one dispatch, upload of `4*N+24` bytes and result
readback of `4*N` bytes per call. Calibration, warmup and trials retain aggregated
counters and checksums. Eligibility changes retain prior CPU fallback separately;
the summarizer only creates prior/new GPU ratios when both actual GPU variants
exist, and separately records prior-CPU/new-GPU complete-route comparisons.

## Frozen identities and completed measurements

Preparation and post-measurement inspection both pass. All 78 archived artifact
hashes and the compiler/methodology hashes match. Controls match their preflight
hashes and the active source files match frozen copies. The 786-member catalogue
is snapshot
`f5ef7bfd79adee16ef47984bd149811cc66dfe7b936820fbd2b68eb0e4170ab9`.
Prior replay applies no laws and preserves original core SHA256
`d4d9509fa51dbcfe2488403671152424bc4ac216f339e088684eb0f69eeaed43`.
Checked core SHA256 is
`0107960ebe96fd5c2463e57169810db8e9ade5e6cd646d34243131c68d2a2f19`:
exactly six fresh applications, one per U32 workload, change all six bodies.
The reviewer separately compared each archived body, rather than relying only
on metadata assertions. All preparation commands succeeded.

Node records 2,772 timed samples and 1,254 exact result comparisons; the headed
browser records 3,276 samples and 1,362 comparisons. Both have 36 measured cells
and 144 Wasm observations. The six workloads use sizes 32/4096/65536 and small/
full-width inputs; only these six U32 representatives are profiled, not all 21
typed law instances. Hardware is Apple M2; browser is Chrome 154 with Apple
Metal-3 WebGPU. Startup and first-call values remain separate from warm calls.

Independent read-only raw inspection checks every trial, warmup and calibration
checksum and normalization, and all GPU counter aggregates and availability
counters. No discrepancy was found. Browser timing contains 72 actual GPU
variant/cells and 504 timed GPU rows, plus 72 GPU calibration and 72 warmup rows.
The 36 original/prior mapped-zip fallback records never become GPU timings.
All six checked functions have shaders; only the three numeric originals and
prior functions do. Summary medians independently match raw trials, interval
shapes are valid, and no mapped-zip prior/new GPU ratios are present. Paired
intervals are the archived exploratory bootstrap estimates; the reviewer did
not independently regenerate them or adjust for multiple comparisons.

At full-width length 65536 in the browser, prior/new runtime JS improves by
1.297/1.303/1.404 for the mapped-left/right/both zip functions, each interval
above 1. The complementary affine recurrence improves JS by 359.64 and Wasm
by 12.039 [11.808,12.434]. Its actual GPU complete call improves by
1.0766 [1.0643,1.1416]. Captured branch and projection GPU intervals at this
size cross 1, and their Wasm intervals also cross 1. Large JS loop-removal
gains therefore cannot be generalized to every backend: ordinary backend
optimization already removes much of the prior word-loop work in some cases.

Across same-backend prior/new comparisons, Node runtime JS has 36 supported
wins, Wasm 10 wins/26 inconclusive, and direct JS 36 wins. Browser runtime JS
has 36 wins, Wasm 8 wins/28 inconclusive, direct JS 34 wins/2 inconclusive, and
actual comparable GPU calls 7 wins/11 inconclusive. No same-backend interval
supports a regression. These counts describe this finite workload matrix, not
a guarantee of benefit for other programs or hardware.

GPU routing nevertheless has concrete regret. For every one of the 18 mapped
zip workload cells, the new GPU route is slower than both the prior JS and prior
Wasm complete route: every prior-CPU/new-GPU interval is entirely below 1. At
full65536, prior-JS/new-GPU ratios are approximately 0.182–0.205 and prior-Wasm/
new-GPU 0.743–0.772. A shader becoming legal is not a profitable route selection;
these observations support retaining CPU execution for these measured shapes.
No automatic routing policy is implemented by this proof batch.

The subsequent `backend-routing.json` receipt compares current checked runtime
JS/Wasm/GPU on matching browser cells, excluding direct JS and handwritten
controls. Independent inspection confirms 36 unique cells, current runtime JS
has the lowest saved median in all 36, and every one of the 72 checked-CPU/
checked-GPU paired intervals lies below 1 (largest upper bound approximately
0.8025). Thus GPU improves over its own prior affine shader while remaining
slower than both current CPU routes on this measured workload matrix. Root
separately regenerated all 756 saved paired intervals exactly; no timing or
source changed for the routing comparison.

Against the original-algorithm handwritten controls at full65536, checked JS is
faster in every workload, but checked Wasm is approximately 1.65–1.75 times slower
than Rust-Wasm in five browser cases. Affine blend is the exception, with Ink/
Rust-Wasm ratio 0.0839 [0.0828,0.0875]. Rust controls may optimize original loops
naturally and reuse their preallocated final destination; the ordinary-array
JS mapped-zip control preserves materialized source stages. An expert already
fused or closed-form implementation is unmeasured. These control styles and
transport differences preclude a general language ranking. Wasm memory evidence
is exported linear-memory highwater only; JS/GPU memory is unmeasured.

Final review passes with these scope and route-profitability limits. Correct
proofs, applicable source rewrites and measured target profitability remain
separate conclusions.
