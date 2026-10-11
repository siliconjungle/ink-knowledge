# Checked keep execution across targets

`app.ink` uses a fixed-key `Option<u64>` keep. The frozen request pair contains
the ordinary physical layout and a maintained cache, plus a checked migration.
All definitions, membership witnesses and universal equations are self-contained;
execution requires no live database or index. `ink check-representation` checks
the supplied bytes independently. This adds no proof-kernel rule.

The producer now handles different post-state roots on Boolean branches. It
substitutes the admitted point-query cache into the predicted branch condition
and proves each branch using ordinary BoolSplit/Substitute/Convert and existing
inductive remove/replace equations. Unsupported conditions/keys still refresh.
These authoring heuristics have no authority; the consumer must check the complete
source observation, all-action relation preservation and snapshot obligations.

From the ink-lang distribution checkout, reproduce proposals outside this repo:

```sh
ink emit-action-model knowledge/research/keep-parity/app.ink -o build/keep-model.json
python3 knowledge/producers/representations.py build/keep-model.json -o build/keep-generated.json --cache-query zero --preserve-cache --compact-queries --delta-query
```

`tests/feature_parity.rs` executes both layouts and migrations on C, Rust,
JavaScript and both Wasm emitters, comparing exact results/checkpoints after
overwrite, removal and abort. It also checks that the cached query body and
overwrite/removal next-state closures do not call encode or table get. This is
structural work-skipping evidence, not an end-to-end speedup or a proof of backend
machine code. Variable-key puts may refresh; arbitrary Int aggregate keeps remain
outside production logical projection. Baseline JavaScript still recomputes keeps;
the explicit checked representation host executes these maintained definitions.
