# Filtered unsigned aggregate alternatives

Current active requests were re-authored for executable-core V8 and universally checked; see `../representation-republication.json` and `producers/research_representations.py --compiler PATH --distribution INK_ROOT`. Historical snapshot counts and timings below describe their original publications and do not transfer to the refreshed requests.

Frozen database requests for `examples/filtered-aggregate.ink`: direct source execution,
query refresh, and individually maintained filtered u64 sum/count. The source syntax
is unchanged; count is expressed as a sum of one per active row because stateful
Ink's existing `count` returns exact Int. Wrapping u64 semantics include overflow.

The delta producer defines row contribution, total fold and insert/replace/remove
differences as ordinary functions. Universal induction proves filter/map/fold fusion
and each update law, including arbitrary constructor lists. The host's sorted unique
table invariant is not an unproved premise used to simplify the laws. Abort and host
failure retain the old reply; successful transitions update the cached reply. Relations
cover every action's full observation and new logical state. Unrecognised updates use
source refresh, never an unchecked delta. Sum and count each have a direct checked
bridge from the direct representation; generic reverse migration uses endpoint proofs.

Generate the source model with `ink emit-action-model examples/filtered-aggregate.ink -o model.json` and
run `producers/representations.py model.json --cache-query total_query --preserve-cache
--aggregate-query -o proposal.json` (or `count_query`). `word_ring.py` emits elementary
word equalities using checked SAT lemmas. `bitvector_proofs.py` supplies untrusted RUP
certificates; all steps replay in the general checker. No compiler aggregate rule is added.

Individual requests and bridges stay below the 16 MB catalogue bound. The combined
pretty-printed authoring output duplicates closures and is not a distribution format.
Tests replay frozen files without producers or SQLite: all seven standalone lanes,
plus native/reference/C/JS runtime histories with rollback, overflow, restoration,
commit exhaustion, acknowledgements and both migration paths.

Performance evidence is separate in `reports/representation-scaling`; a checked delta
is an available alternative, not an automatic selection or guaranteed speedup.
