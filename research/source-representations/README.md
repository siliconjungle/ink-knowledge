# Frozen source-bound representations

Current active requests were re-authored for executable-core V8 and universally checked; see `../representation-republication.json` and `producers/research_representations.py --compiler PATH --distribution INK_ROOT`. Historical snapshot counts and timings below describe their original publications and do not transfer to the refreshed requests.

`app.ink` is unchanged across both selections. `direct.json` stores the source
tables directly in a database-defined tuple. `reversed-query-cache.json` changes
the physical field order and stores the reply of `zero`. Query execution retains
the physical state instead of refreshing that cache. Changes rebuild it through
the encoder. `migration.json` supplies a universally checked conversion.

These are canonical entries in the pinned main store, with self-contained
request bundles and authenticated membership witnesses. The producer is
`producers/representations.py`; it is untrusted. The Ink compiler must check
all definitions and action equations against this exact application's fixed
source transition projection. There is no speed claim or efficient delta
maintenance claim.

`retained-direct.json`, `retained-query-cache.json` and
`retained-migration.json` add a checked work-skipping candidate: ordinary
queries such as `get(key)` return the retained physical state instead of
rebuilding it and refreshing an unrelated cached query. Universal proofs cover
all query arguments and states. The earlier requests remain available for
comparison. The producer defaults to this candidate; `--rebuild-queries`
reproduces the earlier query behaviour for measurement.

Changes still rebuild the cache. This is not delta maintenance. Complete-call
measurements also include runtime/native transport costs and belong in the
distribution's `reports/representation-performance` report; membership or a
timing result never authorises replacement of source semantics.

From an assembled ink-lang distribution:

```sh
ink check-representation knowledge/research/source-representations/app.ink \
  knowledge/research/source-representations/reversed-query-cache.json
ink check-migration knowledge/research/source-representations/app.ink \
  knowledge/research/source-representations/direct.json \
  knowledge/research/source-representations/reversed-query-cache.json \
  knowledge/research/source-representations/migration.json
ink execute-representation knowledge/research/source-representations/app.ink \
  knowledge/research/source-representations/reversed-query-cache.json \
  knowledge/research/source-representations/calls.json
```

Other physical definitions, cache update algorithms and proof producers use the
same contract. Unsupported source semantics need fixed correspondence first;
abstract assumptions, a name, a profile or a membership hash never establish
correctness. Literal Rust lowering and the host remain trusted implementations.

Further change-boundary candidates are in `../cache-maintenance`: aborted changes
and writes to unrelated tables reuse the cached reply, with a compact transition
carrier and universal proofs. The earlier fixtures here remain unchanged.
