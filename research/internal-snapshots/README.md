# Private field updates

`rows.ink` is generated ordinary Ink source for the five-u32 `row-schema.ink`.
Only `reconcile_fields` exposes a logical value. Its field delta builders and
replay helpers use owned buffers and are internal to the invocation.

`rows.laws.ink` authors five universal single-field replay laws. The canonical
catalogue snapshot is
`dcf3c52318c318f993499ec1d513ab7700e1b73fa678c803b7e93d0d1ba3f3fe`.
These laws prove component replay, not an end-to-end snapshot theorem or
profitability. The disposable SQLite index is not part of the stored contract.

From the Ink distribution root, regenerate and check the source and laws with:

```sh
python3 knowledge/producers/field_snapshots.py --compiler target/debug/ink --source knowledge/research/internal-snapshots/row-schema.ink --record Row -o /tmp/rows.ink
```

The producer reads checked declarations and renders their schema closure. It
groups identical carriers in chunks of at most two fields, within portable
context bounds, and accepts at most 64 fields within the law-authoring bound.
Unsupported schemas fail closed. No generated name or hash grants proof authority.

Distribution tests also cover heterogeneous nested fields, exact float bits and
nominal IDs, rehash false replay/declaration mutants, check proofs without the
original module, and compare final values across C, Rust, JavaScript and both
Wasm backends. Small flat JavaScript rows often favour retaining the existing
`after` row over constructing and replaying field updates. Both alternatives
remain available; measurements and proof validity are separate.
