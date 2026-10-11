# Read-only web-stack harness review

Reviewed publisher `producers/publish_web_stack_laws.py`, dedicated
`bench/web-stack-proofs.py`, Ink kernels and JavaScript/Rust/Node/browser assets.
This lane ran no builds, tests or measurements and changed no implementation.

The publisher stages exact canonical objects, checks all new entry roots with the
existing compiler, verifies compiler identity, then publishes the identical
snapshot. It rejects duplicate batch IDs, existing IDs and conflicting names;
checks the requested prior pin; preserves all previous immutable members and the
prior snapshot. Profitability observations are separate from mathematical
admission. No theorem-specific trusted mechanism is introduced.

The benchmark compares unoptimised source, the preserved 648-entry catalogue and
the extended catalogue using the same compiler binary. Original and selected
cores, plans, manifests, shader eligibility and artifact hashes are archived.
The active tasks use wrapping U32; JavaScript uses Math.imul and explicit wrap
for each source multiplication/addition/subtraction. Rust uses wrapping methods
and normal release optimisation. Quadratic/cubic operand association matches
Ink, including both cubic cross terms. Numeric Python closed forms use exact
arbitrary integers modulo 2^32, an independently written implementation.

Each measured implementation captures a typed input once. Wasm paths include
input copying, result conversion and consumption; explicit generated JS and
handwritten JS use the same snapshot/checksum driver. Runtime wrappers remain
included in runtime variants and are reported separately from direct JS exports.
Inputs remain stable during all pure calls. Actual list values are compared to
the complete oracle before timing, with checksums consumed during timing.
Seeded interleaving pairs trials by round; confidence intervals resample those
same round pairs. Startup and preparation are excluded from warm call timings.

GPU fallback records are retained without GPU timed samples. A manifest-eligible
shader must actually execute on the browser GPU to count as a GPU measurement.
Unavailable old shaders cannot support a prior/new GPU speedup claim: successful
new direct-map emission is an eligibility gain in those cells. GPU calls include
upload, allocation, dispatch and readback. Device metadata is recorded.

Wasm observations are limited to exported linear-memory highwater and disclose
that host and GPU memory are excluded. JS/GPU memory is unmeasured, so those
variants cannot create canonical observations requiring measured peak bytes.

Issues raised during review:

1. New-proof attribution: the initial tool required any checked application per
   task, which could be an old law. It now requires a new member per task,
   records IDs by function, and requires every prior/new function body to differ.
2. The initial handwritten self-zip was already written as the selected map.
   It now uses the original indexed self-zip loop with two input reads. Rust
   already used `xs.iter().zip(xs)`.
3. Trusted identity outputs may be typed arrays. The runner now accepts arrays
   and numeric views for full validation/checksum consumption without forcing
   output allocation just for the benchmark.
4. Schema-2 GPU fallback diagnostics now read `fallback_reason` correctly.
5. Requested literal Python evaluation of the new guarded-write and
   repeat-restore source operations, rather than duplicating their closed-form
   oracle shortcuts; requested explicit zero-scan corroboration/disclosure.
6. Requested first validation-call receipts because lazy Wasm instantiation
   occurs before warm cell timing and is absent from module-load receipts.
7. Requested per-function observation entry attribution and active methodology
   hash verification. These improve evidence usability/provenance; the plan
   package itself remains the exact whole-module plan.

All seven items were confirmed resolved in the final source/prepared runner.
Python now executes the restore loop and guarded condition, corroborates the
zero-map scan as a full list traversal, and checks ordered fold with an
independent mapped right-fold against an alternating modular sum. The runner
records `first_validation_call_ms` for initial lazy-Wasm execution. Canonical
entries are attributed to each measured function; the active methodology hash
and exact sample variants are checked.

The final prepared suite has 11 tasks and 66 cells. The author/root reported
1,089 exact Node oracle comparisons before timing; this reviewer read the
protocol and receipts, without rerunning validation or measurements. Original
JavaScript and Rust dispatch once outside inner loops; neither control pays
benchmark case dispatch on each loop iteration. Ordered-fold controls preserve
map allocation and right-to-left subtraction. The independent Python fold
oracle is `sum((-1)^i*x_i*k) + (-1)^n*seed`, modulo 2^32, corroborated by literal
mapped right-fold evaluation including empty and odd-length inputs.

Preparation initially included mutable log files in artifact hashes. Root
removed those untimed log hashes before timing and archived the exact harness
source; the prepared metadata explicitly records that exclusion. Such logs are
not compiler/executable inputs. Existing measured archives were untouched.

No blocking issue remains for measurement. This review establishes protocol and
provenance readiness, not a performance result or a proof of target lowering.
