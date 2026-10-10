# Ink knowledge

Immutable knowledge data for [Ink](https://github.com/siliconjungle/ink-lang), with a rebuildable SQLite discovery index. Search and execution policy live in [ink-planner](https://github.com/siliconjungle/ink-planner); proof checking stays in Ink's independently buildable semantic core. Storage never grants proof authority.

## Storage contract

`store/objects/<sha256>.json` contains canonical entries. Every entry has exactly these fields:

```json
{
  "schema": 1,
  "kind": "rewrite",
  "semantics": "ink-conditional-laws-v1",
  "dependencies": [],
  "interface": {
    "parameters": {},
    "result": null,
    "operations": [],
    "effects": [],
    "conditions": []
  },
  "payload": {}
}
```

Kinds are `definition`, `theorem`, `rewrite`, `implementation`, `representation`, `maintenance`, and `bridge`. The semantics version determines the typed payload and admission domain. Declaring a kind or storing a proof does not implement its checker: unsupported domains reject. Mathematical definitions, scalar theorems, inductive theorems and executable semantic laws use this common entry contract. Program-specific certificates still have specialised proof terms; they are not automatically admitted as executable laws.

Identity is SHA-256 of UTF-8 JSON with lexically sorted object keys, no whitespace, and no trailing newline. Files add one newline for readability. JSON numbers are integers in the shared Rust/Python range; measured durations are decimal strings. Dependencies and index lists are sorted and unique. Display names live separately and have no authority. The Rust checker verifies the typed mathematical interface against the payload.

`store/trees/` contains authenticated sorted leaves of at most 64 IDs and binary branch nodes. `store/snapshots/<id>.json` pins a Merkle root; `store/snapshot.json` selects the current snapshot. A bounded exported view carries selected roots, their exact dependency closure and membership proofs. The core authenticates membership, hashes, semantics, proof terms and applicability. It never needs the complete database. New snapshots do not invalidate replay of a plan carrying an older pinned view.

`store/observations/<id>.json` stores performance evidence separately. Each observation pins program, plan and knowledge IDs; hardware, driver, toolchain, backend and bridge; shape, distribution, concurrency and residency; full-call nanosecond samples and peak allocation. Observations do not change the proof snapshot or become proof premises.

Formal storage schemas are in `schemas/`. Canonicalization, sortedness, hashes, exact dependency closure and mathematical validity require the library/checker in addition to JSON Schema validation.

## Query API

Install with `python3 -m pip install -e .`, or use `PYTHONPATH=.` in a source checkout. Python 3.10+ and SQLite 3.37+ are required.

```python
from ink_knowledge import Store
store = Store('/path/to/ink-knowledge', '/path/to/pinned-snapshot.json')
store.rebuild()
ids = store.query(kind='rewrite', semantics='ink-conditional-laws-v1',
                  operation='binary:+', result={'Value': 'U32'}, limit=128)
view = store.bundle(ids)
```

Queries also support parameter types, effects, exact applicability conditions and an `after` ID for paging. `ink_knowledge/index.sql` specifies the SQLite schema with explicit tables for snapshots, entries, membership witnesses, dependencies, types, operations, effects, applicability, names and observations. Result order is deterministic. Indexed subset export loads only its selected objects and dependency closure, authenticating cached membership witnesses against the pinned root.

```sh
python3 -m ink_knowledge --root . rebuild
python3 -m ink_knowledge --root . query --kind rewrite --operation binary:+
python3 -m ink_knowledge --root . export --entries ENTRY_SHA256 -o view.json
/path/to/ink knowledge-check program.core.json view.json
python3 -m unittest discover -s tests -v
```

`index.sqlite` is ignored and disposable. Rebuilding atomically replaces it from canonical Git objects; a cache from another snapshot is rejected. A future database service must retain this object/snapshot/view contract. The database is an untrusted supplier of proof data, not an authority.

## Authoring and research

`producers/` holds untrusted authoring/import tools. `research/` quarantines historical experiment formats, fixtures and Lean work; production discovery does not scan it or depend on experiment directory names. Research tools can still reproduce their original mathematical experiments. These formats are not compatibility aliases for the canonical API.

The current snapshot contains 658 canonical entries, including 42 executable semantic laws. Earlier snapshots are retained; 20 checked append-view entries, six fixed change-boundary definitions/theorems and 46 general-law entries (`research/general-laws`: abstract sorts, functions and assumptions with eight parametric collection laws) were added without changing the existing rewrite payloads or name targets. The change-boundary laws bind to shared language primitives, but do not certify action bodies or physical rollback. See `research/incremental-views/canonical-review.json` for proof-admission evidence and scope. Reproduce its data with `python3 producers/build_store.py --output /tmp/ink-store`; this explicitly imports the research fixtures as an authoring operation. `store/rewrite-view.json` is a transport fixture for integration tests, not a second storage format or discovery API.

Eleven effect-prefix composition entries add outer path/value/exit definitions,
sequencing and six checked laws. Their definitions bind to the core's fixed
finite composition operation. They are not a source-analysis soundness theorem,
whole-action refinement or authority to skip rollback. See
`research/effect-composition/README.md`. The 42 executable rewrite entries remain
unchanged.
