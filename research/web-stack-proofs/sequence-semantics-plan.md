# Minimal sequence extension grounded in Frontier source

The first extension is ordinary same-type `List<T>.concat(List<T>)`, implemented
as general finite sequence append. Its core implementation is in
`core/src/{core,check,eval,semantic,laws}.rs`, with independent fixtures under
`core/tests/sequence.rs` and a trust-boundary contract in
`docs/sequence-semantics.md`. Backend emission belongs to the independently
versioned JS/C/Rust/GPU packages. The source IR already has a generic Method
expression, so this extension requires no parser or AST special case.

The pinned Frontier source is commit
`2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2` of
`siliconjungle/-shapeshift-labs-frontier`. Its `src/diff.ts` equal-prefix/suffix
loops (lines 4446–4466) motivate reconstructing unchanged prefix and suffix
regions around a changed middle. Its patch sources also preserve ordered writes
and permit empty patches. These are mechanisms to model, not evidence that a
pure list theorem verifies JSON patch paths, exceptions or mutation semantics.
See `frontier-notes.md` for source links and the completed eight pure word laws.

## Why one primitive first

The executable source IR has no Nil/Cons constructor. Those constructors exist
only in semantic proof terms, so the current source grammar cannot already
author a general append function. Concat supplies the missing executable
composition operation and a small definitional bridge to existing list
induction. It can express explicit prefix/middle/suffix composition when those
regions are input parameters. Extracting regions from one input remains future
work; concat alone does not implement Frontier's common-prefix scan or slicing.

The trusted computation extension is only the Nil/Cons append definition.
Existing proof objects can establish associativity, count distribution and
map distribution. Root authors these objects and demonstrates planner replay
after the extended compiler is ready. They are not hard-coded optimizer rules.
No new induction, trusted theorem, JSON-specific operator or proof flag is
needed for this phase.

The executable semantic tag becomes v3 only for programs using concat, with
old v1/v2 bytes stable. Semantic terms and proof objects retain the existing
additive operator schemas; unknown operators are rejected by old checkers.
Updated arity/sort checks and definitional computation are trusted primitive
implementation changes, documented separately from external proofs.

## Correctness and target limits

Both operands have the same element type, evaluate once left-to-right and
produce their elements in order. The outer result is fresh. Element values,
including F32 bit patterns, remain unchanged. Core typing is generic over
already admitted list types, while packed C/Wasm layouts initially cover
their existing flat numeric/Bool/vector/record subset. JS supports its existing
general value representations. Unsupported target layouts must be reported.

Append has no indices. Finite sequence length addition is mathematical, with
physical overflow/allocation reported as execution failure, never U32
saturation. Existing U64 count wrapping and existing indexed operator policies
remain unchanged. The reference evaluator charges ordinary evaluation/copy
cost plus outer-list append work. Resource failure is outside pure successful
value equivalence and is not hidden in theorem conditions.

Independent core correctness tests use explicit indexed sequence oracles,
including empty boundaries, full-width integers, float bits, nested values,
type and semantic-wire rejection. Backend correctness fixtures compare exact
results and preserve input arrays. Existing false-proof controls remain part
of the trust-boundary validation. Source edits waited for the frozen 52-law
Node/browser measurement to complete before any test/build job. The standalone
core regression now passes: 20 existing unit tests and four new sequence tests,
archived in `sequence-core-tests.log`. Backend validation, external concat law
admission/replay and new measurements remain separate stages.

GPU has an explicit unsupported-concat fallback initially. The benchmark must
record source and selected backend plus fallback reason, and include transfer,
dispatch and readback only when actual GPU execution occurs. It may legitimately
show a law changing eligibility, but cannot call a CPU/GPU comparison a
two-shader speedup.

## Profitability and the next extension

Concat reassociation has shape-dependent copy costs. With materialized outputs,
`(xs.concat(ys)).concat(zs)` copies `2|xs|+2|ys|+|zs|` outer cells, while
`xs.concat(ys.concat(zs))` copies `|xs|+2|ys|+2|zs|`. The latter helps when the
prefix is longer than the suffix; it can be slower for the opposite shape.
Map distribution/fusion similarly trades callback evaluation and intermediate
allocations. Matched source and checked modules, independent literal controls,
asymmetric sizes and consumed outputs are required before claiming a win.

General `take`/`drop` or `slice` can follow. They require a separate policy for
U32 boundaries, out-of-range saturation, half-open ranges and list lengths,
and their useful composition proofs may need induction with changing bounds.
That is broader than this append extension. Avoid shipping names whose source
semantics or proof obligations the checker cannot yet express.
