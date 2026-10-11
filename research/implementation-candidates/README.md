# Point-query implementation candidates

Current active requests were re-authored for executable-core V8 and universally checked; see `../representation-republication.json` and `producers/research_representations.py --compiler PATH --distribution INK_ROOT`. Historical snapshot counts and timings below describe their original publications and do not transfer to the refreshed requests.

This immutable experiment publication packages ordinary point-query emission
and the existing maintained representation as database implementation entries.
`publication.json` identifies the snapshot, supplied baseline, candidate and
original source. `candidates.json` is the external planner index.

The ordinary entry contains an empty `ink-evidence-v1` selection; the maintained
entry contains the existing `ink-source-representation-v1` package and universal
proof bytes from `../point-delta/delta.json`. Neither entry gets compiler authority
from its name, ID or membership. The planner and replay tool invoke the existing
checker for its package before emission. Algorithms/proofs remain database data.

Reproduce with `producers/implementation_candidates.py --knowledge-root
research/implementation-candidates --identity-source SOURCE --package
research/point-delta/delta.json`, using the source ID in `publication.json`.
The generic producer can publish other source selections or representations,
without recognising this program or its table/cache operations. Publication
extends an existing snapshot instead of dropping prior entries or names.

Measurement IDs bind each entry, exact compiler executable and emission lane;
this publication supplies no profitability measurements. Synthetic integration
costs test policy separately. Its pinned snapshot remains usable after later
publication and disposable-index rebuilding.
