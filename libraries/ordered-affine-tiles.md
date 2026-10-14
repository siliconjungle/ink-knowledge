# Ordered affine word folds

`producers.ordered_affine_tiles` constructs an ordinary checked equality for
`foldr(xs, seed, fn(x) => fn(acc) => x + acc * k)` over wrapping u32 values.
Each ordered tile computes a pair `(bias, scale)`; a second right fold combines
these summaries in source order. List reconstruction, ordered fold splitting,
conditional drop composition and the affine equations replay in the existing
checker. There is no new theorem whitelist, primitive, core recogniser or runtime
profitability probe. Numeric width is explicit in reconstructed carrier constants.

The default proposal uses 16 tiles of 4096 elements. A literal ordered suffix
handles every element beyond 65536, so correctness is not restricted to the
benchmark size. Dimensions are compile-time choices. This is bounded parallelism,
not an asymptotic scaling claim; small inputs can be slower. Floating-point,
nonlinear and arbitrary order-sensitive reductions are outside this law.

The producer is in the normal proposal catalogue. Matching only filters proposals;
all dependency proofs replay before selection. Structural prices need not prefer
tiling. Select from comparable complete-call measurements using the planner's
measured-selection guard; retain the source when evidence is missing. Keep the
runtime backend fixed. Proof establishes equality, not device eligibility or speed.

Replay and regenerate the portable example:

```sh
PYTHONPATH=knowledge python3 -m producers.ordered_affine_tiles \
  --compiler target/debug/ink -o build/ordered-affine
INK_COMPILER=$PWD/target/debug/ink PYTHONPATH=knowledge:planner \
  python3 -m unittest knowledge.tests.test_ordered_affine_tiles
```

The installed compressed support data is the canonical closure also recorded in
`proofs/ordered-affine-support/view.json`. Its scalar slice facts carry checked
bitvector certificates; the sources are `ordered-slice-laws.ink` and
`slice-arithmetic-laws.ink`. The dependent construction is reproducible Python
authoring data. Rehashing an altered target does not make the old proof valid.
