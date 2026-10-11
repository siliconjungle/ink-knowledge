# Executable work-skipping laws

`producers/performance_laws.py` authors 47 canonical rewrite objects for the
existing `ink-conditional-laws-v1` checker. The isolated snapshot in `store/`
contains only these laws. Production publication is a separate operation.

The new families are universal repeated subtraction, repeated addition of a
product, identity/cancelling loops, sum of scaled/zero maps, U64 constant-map
sum, count after map, always-true/false filtering, repeated-filter idempotence,
and filter fusion. Word arithmetic wraps at its declared width; no F32
arithmetic identities, reassociation, or state effects are claimed. The
collection laws rely on Ink's pure total value semantics.

Proofs use the existing natural/list induction, Boolean cases and normalization
mechanisms. There are no new trusted rules or compiler pattern recognisers.
`manifest.json` records display names and canonical IDs. `view.json` carries the
authenticated proof bytes.

From the knowledge checkout, reproduce admission and application evidence with:

```sh
python3 research/performance-laws/verify.py --compiler ../target/release/ink
PYTHONPATH=. python3 -m unittest tests/test_performance_laws.py -v
```

`validation.json` records the compiler hash, admission of all 47 laws, checked
planner replay on 11 U32 patterns, and rejection of two hash-valid forged
bundles. The forged examples change a proven zero result to one and remove a
required induction proof. Their rejection comes from semantic checking, not
content-hash mismatch.

The multi-function validation fixture requires a larger search budget than the
default 128 attempts to select every law. Use budget 4096 to reproduce the full
selection. Search costs are structural estimates; these files contain no timed
performance measurements. JavaScript, WebAssembly, WebGPU and Rust comparisons
belong in the separate benchmark reports and performance observations.
