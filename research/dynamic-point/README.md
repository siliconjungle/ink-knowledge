# Dynamic-key point maintenance

Frozen source-bound direct and delta requests, and a direct-to-delta migration.
The model is produced from `source.ink` by `ink emit-action-model`. Run the
external `producers/representations.py` with `--cache-query zero
--preserve-cache --dynamic-delta` to reproduce the proposal. The compiler
specified by `INK_COMPILER` creates scalar obligations; `python-sat` supplies
untrusted certificates that the Ink checker verifies.

Every table constructor, including unordered and repeated keys, participates in
the induction proofs. Remove and replace repair the old cached Option under the
exact key equality guard. Insert refreshes from its precise post-state at the
queried key and otherwise reuses the old reply. Branching upserts, aborts,
host failures and chains are covered by complete action preservation proofs.
The tactic currently targets fixed `u64` queries with dynamic `u64` update keys.
Unsupported action shapes retain the exact refresh fallback.

The Rust integration test checks both requests and migration, follows 194 source
calls, restores repeatedly, then compares standalone backend histories, events
and exact snapshots. It also rehashes and republishes a deliberately false
invalidation guard; authentication succeeds and mathematical admission fails.
`tests/test_dynamic_point.py` compares reproduced bytes with these frozen files.
Correctness does not imply profitability; no default selection is changed.
