# Frontier CRDT source pass

Read-only source pinned on 2026-10-10:

- Repository: https://github.com/siliconjungle/-shapeshift-labs-frontier-crdt
- Commit: `507b8b4ebd659efd25f1d528733ec5937d0d6d7e`
- Local cache: `/Users/james/Documents/ChatGPT/3d-modelling/research/frontier-crdt-source`
- Package version: 0.1.5. No Frontier files, builds or measurements changed.

## Actual mechanisms

`src/crdt-update.ts:208` filters operations by an actor state vector before
encoding the residual update. Spanning operations crossing the acknowledged
sequence are shortened rather than dropped (`getOperationsSinceStateVectorFromList`,
around line 985). This distinguishes a covered whole operation from a covered
prefix of an operation.

`filterCrdtUpdates`, around line 222, combines per-update decode, predicate
filtering, deduplication and retained-operation collection. It performs the final
sort and encode once. `mergeCrdtUpdates`, around line 253, similarly collects
missing operations using actor ranges and an exact ID set, then conditionally
sorts. `appendMissingOperation`, around line 940, handles spanning-operation
overlap as well as single-operation IDs.

## Transfer classification

| Idea | Status for this Ink batch | Reason |
| --- | --- | --- |
| Fuse filters/traversals before final materialization | reference, partly already covered | Existing generic filter fusion/idempotence laws and the new map fusion/fold batch capture pure traversal fusion. Renaming those laws would not add mathematical content. |
| Skip updates entirely below an acknowledged actor sequence | needs-revisit | Requires a model of actor IDs, intervals, sequence slicing and encoded-update semantics. A scalar comparison alone cannot prove CRDT update equivalence. |
| Trim the acknowledged prefix of a spanning operation | needs-revisit | Whole-operation filtering is insufficient; a proof must retain the exact residual operation and causal metadata. |
| Exact duplicate operation elimination | needs-revisit | Current pure list semantics lack operation identity sets and causal metadata. Dropping repeated arithmetic updates is generally wrong; no such rewrite was introduced. |
| Sort only when needed, encode once | reference | Ordering and byte-format semantics must be specified before proving an encoded-output replacement. |

The README describes broader lattice helpers, but this pinned extracted source
does not include a `crdt-lattice.ts` or exported lattice subpath in package.json.
This pass relies on the available update implementation. It makes no claim
that Frontier CRDT itself has been formally verified or sped up by this work.

The core Frontier diff/apply pass and its checked pure no-op models are described
in `frontier-notes.md`. Those small models must not be mistaken for proofs of
the full mutable JSON or causal CRDT implementations.
