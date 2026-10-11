# Ordered sequence harness review

Read-only review, 2026-10-10. Scope: `bench/sequence-proofs.py`, its five assets,
`producers/web_sequence_laws.py`, `producers/select_sequence_laws.py`, and the
actual compute-host capture/transport path. No compiler, test, validation or
timing jobs were started in this review.

## Finding to resolve before freezing inputs

The handwritten `concat_empty` control initially used
`Array.from(ys).filter(x => false)`. This materialises a full extra list before
the source filter stage. Since the captured input is a Uint32Array and the
concat helper accepts typed arrays, `ys.filter(x => false)` implements the
original stages without that extra copy. The issue was sent to the harness
author and parent before preparation. It affects control fairness, not oracle
correctness. The active harness should also be copied into the prepared report
as `harness.py`, preserving its independent Python oracle and audit code with
the artifact hashes.

## Reviewed correctness and attribution

- All five sources use both input lists with their declared order. Ordered
  fold is right fold of `x - accumulator`, starting at the supplied seed. Its
  independent closed form is the alternating sum starting with `+xs[0]`, plus
  seed with sign `(-1)^length`. The literal Python implementation traverses
  the concatenation backwards and wraps every subtraction. Empty and odd
  boundary fixtures exercise the seed sign.
- The map oracle masks each multiplication to U32; the JS control uses
  `Math.imul(... ) >>> 0`. Sum wraps every addition in the source-stage
  evaluator; the independent unbounded-integer sum masks only the final value,
  which is equal for wrapping integer addition. No float reassociation is
  introduced.
- Count returns source U64. Direct JS/control values use BigInt; runtime U64
  presentation may return a safe Number or decimal string. Exact decimal
  comparison and `BigInt(value)` consumption preserve equality. List checksums
  contain U32 sum and positional sum packed into a U64 code; accumulation uses
  `BigInt.asUintN(64, ...)`, matching Python's modulo-2^64 audit. Fixture list
  sizes stay below JS precision/index concerns.
- The 32 laws comprise five-type sequence associativity, left/right empty
  removal, count and map fusion; integer sum splitting; and ordered fold
  splitting for the four non-Bool numeric types. Fold splitting keeps the
  right-list fold as the left-list fold's initial accumulator, preserving the
  exact operator order, including F32. F32 sum splitting is deliberately
  absent. Empty removal proves equality of pure values, not pointer freshness
  or mutable alias policy; selected identity outputs can borrow values under
  the trusted pure caller contract.
- The selection helper matches each named law against the exact emitted
  semantic function body, binds every parameter, requires membership in the
  pinned store, embeds the membership bundle, and runs local `check-selection`
  before writing the candidate. Preparation checks again and reifies the
  selected core before emitting either backend bundle. Explicit selection is
  a checked alternative for measuring profitability, not a claim that the
  current structural cost planner can rank these copy-saving rewrites.
- Prior700 and checked candidates use the same compiler path/hash and the
  same original core. Copied prior/current stores must preserve their exact
  pins. Per-function attribution requires a newly added law ID and an actual
  difference between prior-selected and checked-selected function bodies.
  Changing the source alone cannot satisfy these checks.

## Full calls, fallback and evidence

Both resident typed lists are captured once per complete call. CPU and GPU
requests pass the originals to the runtime; packed U32 ingress creates one
`.slice()` snapshot per list. Explicit trusted JS, direct generated JS and
handwritten JS each take two driver snapshots, with no runtime recapture on
the explicit JS path. CPU then pays its Wasm `.set()` transfer, C operations,
output copy before arena reset, and public result conversion. Each timed call
is awaited and its result is consumed inside the timer. Calibration, warmup
and rounds randomise variant order using a reproducible seed.

All five current tasks are expected to lack GPU shaders. Direct concat,
ordered scalar reductions and identity output use CPU fallback; map over a
concat receiver is also outside the current direct-input-array shader subset.
The runner records actual backend/reason/counters, validates fallback values,
and admits a GPU timed variant only when its actual backend is GPU. The audit
rejects fallback-labelled GPU samples and rejects an eligible shader that did
not actually execute. An absent prior/new GPU ratio therefore remains
unavailable/fallback and cannot be described as a GPU speedup.

Canonical observations are created only for Wasm variants that expose linear
memory highwater. The bridge/toolchain/driver explicitly scope that metric;
host and GPU memory are unmeasured. Each observation lists only law IDs
applied to its own function. No memory figures or canonical JS/GPU observations
are invented. Raw prepared source, fixtures, selections, receipts, bundles,
first-call records, warmups, calibration and samples remain separate from the
proof store and profitability claims.

## Final independent receipt review

Reviewed the prepared stage-two Node/browser summaries, metadata, publication,
all-law admission and selection-check receipts, typed all-law source, selected
executable core and observation import receipt. No tests, measurements or
interval calculations were rerun. The earlier fairness issue is resolved in
the archived literal control (`ys.filter(false)`), and `harness.py` is archived
with its metadata hash. No blocking review finding remains.

The all-law receipt admits all 32 concat equations under isolated pin
`cbc4c19c4979e1c2c99d5691e36bf17cbca416c2ec36ef124dc2ceab6e890017`;
the matching replay lists all 32 applied IDs and a changed selected core. The
archived selected executable core includes actual typed replacements for every
law family, including curried ordered folds and exact F32 operation order.
Publication adds these 32 to prior700, yielding 732 at pin
`52f1b3564ceb41b36a12ae6fca2d067e1bd2a11ec64ab3556d31ef6cdd37e12b`.
This semantic/proof coverage exceeds the five U32 tasks used for profitability
measurement; it does not establish performance of all 32 type instances.

The measured candidate applies one named new law per function, with actual
body changes in all five functions. Prior700 applied no laws and retained the
input core hash. Both use compiler
`45670dbced0999e945278d7de7ed495cad9b43b1ab9d24c27182c9f9a5683e08`,
which is the new concat-capable compiler, separate from the earlier 52-law
experiment. Explicit checked alternatives were forced for measurement because
the structural planner cannot rank these allocation savings; these results
do not show automatic planner discovery or general language superiority.

Each host records 30 cells and 1470 paired samples; exact oracle comparisons
are 560 Node and 620 browser, with 50 independent complete-fixture Python
literal checks. At browser full-65536, archived prior/new JS ratios are
6.95× count, 1.27× ordered fold, 8.26× sum, 1.28× empty removal and 1.10× map
fusion. Wasm gains are smaller: 1.07× count, 1.09× fold and 1.15× sum have
intervals above 1, while empty/map intervals cross 1. These are complete calls
with both snapshots, transport, conversion and consumed outputs still paid.
The archived Node results differ and retain their own uncertainty intervals.

All ten prior/checked GPU manifest entries are shader-ineligible, and both
summaries contain only CPU/control timed variants. Browser fallback checks
increase validation coverage but establish no GPU performance claim. The
canonical import receipt records 120 unique measured Wasm observations,
2102→2222, at the unchanged732 proof pin; host/GPU memory remains unmeasured.
Earlier native C/Rust and GPU-fallback tests are documented separately in
`sequence-backend-tests.json` as a truthful reconstruction of their successful
tool outputs, with no new test run and no invented raw log or source hash.

Receipts and sources: `reports/sequence-semantics-2026-10-10/{metadata.json,
publication.json,node-summary.json,browser-summary.json,proof-tests.log,
canonical-observation-import.json}`, and `proof-replay/{all-laws.ink,
admission.json,selection-check.json,selected.core.json}` beneath that report.
