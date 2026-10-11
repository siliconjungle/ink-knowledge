# Checked Frontier-inspired representations

These are source-bound proposals authored by untrusted Python tactics and checked
by Ink's existing general equality/representation/migration checker. Hashes and
producer pattern matches grant no replacement authority. Kernel rules and proof
resource limits are unchanged.

| Directory | Candidate and scope |
| --- | --- |
| `grid` | Exact derived cache of the unchanged A* result, including path, expansion count and limit flag; no pathfinder or tie-order substitution. |
| `heap` | Exact derived cache of the unchanged heap sort, preserving order, duplicates and empty/maximum-word inputs. |
| `mutations` | Direct per-column insert/remove/replace, including Boolean word fields. Every logical sequence is covered, including duplicate/unordered keys. |
| `fields` | Fixed-key Option field cache. Replacement preserving the actual projection retains its value; read-field changes repair it. Captured mappers and dynamic-key field preservation are outside this tactic. |
| `shared` | Product of two independent caches consuming one complete checked observation. All component relations remain proved; physical roots can still be duplicated. |
| `ordered` | Exact per-row list contributions for parameterless filter/map queries, concatenated in source order. Global/cross-row computations fail authoring. |
| `grouped` | Record of exact u64 filtered sums/counts over an explicitly source-defined group domain. This does not discover an unbounded group set. |
| `fused` | Universal scalar aggregate fusion lifted through the complete unchanged source query. Explicit singleton Boolean cases avoid intermediate list construction. |
| `dense` | Base columns plus at most 16 prepared Option slots for keys 0..N-1, with exact first-match fallback for every other key. Mutations rebuild the slots; no range premise. |
| `index` | Base columns plus stable even/odd key buckets. First-match lookup is preserved for duplicate/unordered rows. Physical mutations rebuild both buckets. u64 keys only. |

Every directory contains the exact source, a manifest binding decompressed bytes,
a compressed model, two complete representation requests (plain-to-index for dense/bucket fixtures) and both proved
migration directions. Gzip has a zero timestamp for deterministic archives.
Archives are transport; the decompressed requests must still be checked. Model
IDs bind the complete source module, not the pathname or producer revision.

Reproduce from an Ink workspace with its exact compiler and proof dependencies:

```sh
INK_COMPILER=/absolute/path/to/ink python3 producers/freeze_frontier_extensions.py --workspace /absolute/path/to/ink-workspace
```

`tests/test_frontier_extensions.py` reproduces candidate objects and rejects
reauthenticated false singleton, ordered-contribution, dense-slot and bucket proposals.
Complete backend action histories, snapshots and migration tests belong to Ink's
`tests/representation_parity.rs`. Profitability and losing candidates are retained
separately in the workspace's `reports/frontier-extensions`.
