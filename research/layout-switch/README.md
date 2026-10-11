# State-reusing representation switches

Current active requests were re-authored for executable-core V8 and universally checked; see `../representation-republication.json` and `producers/research_representations.py --compiler PATH --distribution INK_ROOT`. Historical snapshot counts and timings below describe their original publications and do not transfer to the refreshed requests.

The compact-query measurements favour different implementations for different
executors. `../compact-queries/previous.json` and `../compact-queries/cached.json`
have identical physical datatypes and abstraction relations. Recomputing the
cached reply when switching between these implementations is unnecessary.

`forward.json` and `backward.json` supply canonical database bridges between
these exact endpoints. Their function returns its physical argument unchanged.
The universal migration proof derives each destination relation from the matching
source relation using the existing equality rules. The untrusted producer restricts
proposals to identical source objects, logical/physical sorts and relations;
actual source admission and proof checking remain the core's responsibility.

The runtime still decodes both states, validates logical transport and compares
logical equality before installing the destination. Versions and pending events
survive. Native execution still transports the complete physical term; this is
encoder/cache recomputation avoidance, with no measured migration-latency or
constant-time claim. Selection stays explicit. No syntax, kernel or backend rule
is added, and automatic representation selection remains future work.

The two bridges and shared identity function add three entries. The new 848-entry
snapshot is `87357b19d8fdbe5832da67dd58d1fa1a1d35220efb264319708935fe9eb7defa`.
Earlier endpoint requests keep their original pinned snapshots and remain replayable.

From ink-lang:

```sh
python3 knowledge/producers/representation_bridge.py \
  knowledge/research/compact-queries/previous.json \
  knowledge/research/compact-queries/cached.json -o /tmp/layout-switch/forward.json
ink check-migration knowledge/research/compact-queries/app.ink \
  knowledge/research/compact-queries/previous.json \
  knowledge/research/compact-queries/cached.json \
  knowledge/research/layout-switch/forward.json
```

Exchange the endpoint arguments to propose/check the backward bridge. Runtime
callers pass the checked bridge to `Session::migrate_direct`. Frozen native tests
verify future action histories, cached Some/None, rollback, events, exhausted
versions and failed-switch atomicity. An execution counter verifies that direct
switching never invokes an encoder, while generic migration invokes one. A
rehashed false preservation proof fails mathematical checking.
