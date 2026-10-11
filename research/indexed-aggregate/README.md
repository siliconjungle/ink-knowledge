# Checked indexed storage with filtered sum/count

`request.json` is a compact authenticated immutable view of the database, pinned
independently of the active catalog. Recheck it against
`examples/filtered-aggregate.ink` with `ink check-representation` before lowering.
The producer and admission receipt record all entry names and exact identities.

The physical sequence tree preserves arbitrary order and duplicate keys; cached
u64 aggregates use wrapping arithmetic. Range pruning, insertion rotations,
metadata maintenance, encoding and decoding are ordinary checked definitions and
proofs. Whole-action obligations cover complete source outcomes and a preserved
relation for subsequent calls. CPU backend parity also checks portable snapshots,
events, rollback, acknowledgements, restoration and exhausted versions.

The active database retains this view's immutable snapshot and tree witnesses.
A compact leaf packing changes authentication overhead only, without changing the
membership schema or adding mathematical authority. The database producer never
publishes a candidate as checked until the source-bound compiler replay succeeds.

`direct.json` supplies the comparison representation. `implementations.json`
records ordinary source, direct and indexed database-package IDs for the existing
external implementation selector. Measurements and replay receipts live in the
distribution's `reports/indexed-aggregate-durable/` directory. A compact pinned
direct-to-indexed bridge is reconstructed from `migration-admission.json`'s
`view_snapshot` and `migration` IDs using `Store.bundle([migration])`; wrap that
bundle as `{root: migration, knowledge: bundle}` and use canonical JSON plus a
trailing newline. Its byte hash must equal the admission receipt before replay.

The representation requests bind executable-core V8 after universal replay of an
identical action projection. `producers/rebind_representations.py` performs this
external authoring step; projection equality does not replace kernel checking.
