# Shared physical spine ownership

`SharedSpine.lean` models the detachable recursive edge used by the standalone
native typed-storage emitter. Each live recursive edge contains a reference;
`None` is private destruction state after `take`. The shape is structural: an
empty base constructor and exactly one recursive field in every other
constructor. No database entry identifier selects this lowering.

Lean checks value roundtrip, one-time detachment, payload decomposition during
release, preservation of a shared suffix, positivity of surviving owner counts
and zero replacement allocations in the release model. There are no `sorry`
proofs or new axioms. Compile with Lean 4 (locally checked with 4.35.0-rc4); the
distribution also replays this file through its independent Lean CI checker.

The model assumes acyclic live edges and accurate reference counts. Rust's
`Option<Arc<T>>`, standard Arc implementation, code emission and target toolchains
remain trusted. This is not a proof of compiler correctness. Existing Ink
representation/source/action proofs are unchanged because the immutable values,
checked definitions and externally observed table order are unchanged.

Generated native tests retain a shared 100000-node table, release one copy,
inspect all retained values, then release the last copy. They require zero
allocations, exact deallocation counts, pointer-sized optional edges and a
1 MiB stack. Cross-target representation histories additionally check C, Rust,
JavaScript, both Wasm targets and both GPU hosts, including portable snapshots,
rollback, nested values and exact integers. Recursive state executes on GPU
hosts; this change does not provide unrestricted device coverage.

This removes avoidable work while reclaiming replaced table paths. It leaves
persistent-list update traversal and path reconstruction linear in table size.
It does not by itself make writes competitive with a handwritten balanced tree.
