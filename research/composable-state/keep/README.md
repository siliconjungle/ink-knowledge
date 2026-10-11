# Current source-bound keep fixtures

These complete, self-contained requests and migration are checked against the
current executable-core image of `app.ink`. The previous keep-parity artifacts
remain immutable historical evidence; their original source image does not match
the current integrated compiler's image and is not silently rebound.

Reproduce from the distribution checkout:

```
ink emit-action-model knowledge/research/composable-state/keep/app.ink -o build/keep-model.json
python3 knowledge/producers/representations.py build/keep-model.json -o build/keep-proposal.json --cache-query zero --preserve-cache --compact-queries --delta-query
```

Extract `requests[0]`, `requests[1]` and `migration` from that proposal. Each future
state, complete source observation, codec roundtrip and migration must pass the
normal compiler checker. Producer classifications and SQLite rows have no proof
authority. Current point repair handles parameter keys and pure field projections;
unsupported changes refresh. Queries retain the admitted physical state.
