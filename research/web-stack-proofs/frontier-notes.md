# Frontier source pass: pure no-op write proofs

Source fetched on 2026-10-10: [siliconjungle/-shapeshift-labs-frontier](https://github.com/siliconjungle/-shapeshift-labs-frontier),
commit `2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2`, package version 0.1.9.
Read-only checkout: `/Users/james/Documents/ChatGPT/3d-modelling/research/frontier-source`.
The checkout has no AGENTS.md, perf-wiki search command, research registry or
CRDT source; none was invented or installed. Its existing performance study was
read for context, and historical numbers were not treated as current Ink results.
The checkout remains clean.

## Grounded mechanisms and decisions

| Actual source mechanism | Transfer to Ink | Decision |
|---|---|---|
| [Equal scalar/reference prefix and suffix trimming](https://github.com/siliconjungle/-shapeshift-labs-frontier/blob/2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2/src/diff.ts#L4446) skips unchanged cells and preserves signed-zero distinctions. | Word-value same-value writes can be omitted. General prefix/suffix slicing needs primitives absent from this proof surface. | measured for eight pure word laws and tests; general slicing needs-revisit |
| [Empty immutable patch returns the input](https://github.com/siliconjungle/-shapeshift-labs-frontier/blob/2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2/src/apply.ts#L287). | Zero repetitions and an empty guarded-write fold must preserve the initial value. | measured as proof corner cases |
| [Same-parent mutable sets execute ordered writes](https://github.com/siliconjungle/-shapeshift-labs-frontier/blob/2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2/src/apply.ts#L255) and [immutable object-field patches clone a parent then apply sets](https://github.com/siliconjungle/-shapeshift-labs-frontier/blob/2c72dbb4030e2695b682d3e49ec82d8c5c8ffec2/src/json-patch.ts#L248). | A restricted pure model in which every write restores the exact initial word can remove the entire write sequence. | measured for repeat and guarded-fold proof applications |
| Cached path prefixes, dirty-row planning, string-copy search and adaptive text alignment. | Ink lacks the JSON path, string/splice, dirty-row certificate and edit-distance proof primitives to certify these mechanisms here. | reference / needs-revisit |
| Bitmap or causal CRDT optimisation. | No bitmap/CRDT implementation was found in this extracted Frontier checkout; do not attribute such mechanisms to it. | reference only; separate pinned sources needed |

Here **measured** means executable proof/test evidence was added, with no core
change. It does not mean runtime performance improved. The new laws prove pure
word computations, not Frontier's complete JSON diff/apply implementation, path
validation, mutation, clone policy, root identity or failure behaviour.

## New checked laws

The producer is `producers/web_frontier_laws.py`; names are discovery labels.
The mathematical authority is the locally checked object bytes.

| Family | Exact equality | Types |
|---|---|---|
| Guarded same-value write | `choose(x == k, k, x) = x` | U32, I32, U64 |
| Repeated restore of initial value | `repeat(n, x, fn(i) => fn(acc) => x) = x` | U32, I32, U64 |
| Guarded same-value fold | `foldr(xs, k, fn(x) => fn(acc) => choose(x == k, x, acc)) = k` | U32, U64 |

The guarded laws split on equality and use the existing `AssertEquality` proof
constructor. The repeat uses natural induction and retains `n = 0`; unlike the
old identity-repeat rule, its body refers to the fixed initial value rather
than the changing accumulator. The fold uses list induction, with its equality
premise following the induction hypothesis. F32 is deliberately excluded:
numeric equality does not imply bit equality for signed zero or exceptional
payloads. All functions are pure and total within Ink value semantics.

The isolated eight-law snapshot is
`65c538a0f5d3eff1d9098551caaf844a2b7b910332dc4c2d2d58a743c08e8faa`.
All IDs are recorded in `frontier/store/manifest.json`.

## Admission and practical application evidence

`frontier/admission.json` admits all eight. `frontier/replay.json` independently
replays all eight applied IDs, including two applications under actual map
bodies. `frontier/tests.log` records three passing tests: determinism and no old
statement duplicates, admission/replay with a pinned old-catalogue control, and
two hash-valid false controls rejected for unequal semantic normal forms.

The old 648-entry snapshot
`3ba66adca49bc68eee035c2addecf55cea8a9533d25741dc9d48f5d24a213be1`
applies no laws to the same ten-function fixture and retains its exact core
identity. The new isolated store changes the selected core and eliminates the
guarded writes, repeats and folds. `frontier/old-selection.json`,
`frontier/old-planner.json`, `frontier/old-replay.json` and the new equivalents
preserve that comparison. This establishes new reach for this pinned planner
run, not mathematical impossibility of deriving the result from other premises.

The rejected guards mutate the false branch to `x + 1`; the rejected restore
changes each write to `x + 1`. Their objects have valid content hashes, so the
test distinguishes semantic rejection from corrupted storage.

## Benchmark handoff

These source forms retain an outer map after checking, permitting a comparison
of two actual GPU shaders if the backend admits both:

```ink
fn frontier_guarded_write(xs:List<u32>,seed:u32,factor:u32)->List<u32>{
    return xs.map(fn(x)=>choose(x==seed,seed,x)+factor);
}
fn frontier_repeat_restore(xs:List<u32>,seed:u32,factor:u32)->List<u32>{
    return xs.map(fn(x)=>repeat(512,x,fn(i)=>fn(acc)=>x)+factor);
}
```

Checked results are `xs.map(fn(x)=>x+factor)` with wrapping U32 arithmetic.
Use empty, singleton, full-width and measured-size inputs; include both matching
and nonmatching values for `seed`. The JS/Rust literal controls retain the
original guarded expression or repeat, while their normal compilers may remove
the redundant computation. GPU upload, dispatch and readback may dominate, and
WGSL compilation may already eliminate the source work. No runtime improvement
is claimed by this lane; timed work belongs to the shared benchmark harness.

## Reproduction

From ink-lang, with the existing release compiler and no rebuild:

```sh
python3 knowledge/producers/web_frontier_laws.py --output-store knowledge/research/web-stack-proofs/frontier/store
target/release/ink emit-core knowledge/research/web-stack-proofs/frontier/input.ink -o knowledge/research/web-stack-proofs/frontier/input.core.json
target/release/ink knowledge-check knowledge/research/web-stack-proofs/frontier/input.core.json knowledge/research/web-stack-proofs/frontier/store/view.json
python3 planner/plan.py --compiler target/release/ink --core knowledge/research/web-stack-proofs/frontier/input.core.json --knowledge-root knowledge/research/web-stack-proofs/frontier/store --snapshot knowledge/research/web-stack-proofs/frontier/store/store/snapshot.json --budget 4096 -o knowledge/research/web-stack-proofs/frontier/selection.json
target/release/ink check-selection knowledge/research/web-stack-proofs/frontier/input.core.json knowledge/research/web-stack-proofs/frontier/selection.json
cd knowledge
PYTHONPATH=. python3 -m unittest tests.test_web_frontier_laws -v
```

No canonical snapshot was published by this lane, no Frontier source was
modified, and no compiler/runtime change, build or timed benchmark was run.
