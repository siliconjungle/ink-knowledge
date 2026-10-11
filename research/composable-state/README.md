# Composable state evidence

Canonical `state-calculus/` names expose parametric repair, exact key guards,
field preservation, stable partition storage, shared ordered folds, filtered/grouped
aggregate deltas, stable join and bounded top-k laws. Assumptions are interpretation
obligations; they cannot authorise a closed source rewrite on their own.

`admission-final.json` records mathematical checking with the final compiler.
`representations-admission-final.json` records complete source-bound candidate
admission; the earlier receipts retain their original compiler and snapshot pins. Current physical candidates are
named `composable-representations/…` in the canonical snapshot. The final admission
adds source-bound group mathematics under `composable-mathematics/…`. `compiler-replay-final.json` rechecks the same canonical objects with the rebuilt
compiler and retains the earlier artifact receipts. Reproduction lives
in `producers/`; proof certificates are data and must always be replayed by core.

Word/guard/partition certificates are immutable authoring caches, not axioms. Their
closed CNF goals, bit coverage and refutations are checked locally. Ordinary replay
needs no SAT solver. A missing authoring certificate may require the authoring SAT
dependency; it never becomes an unchecked assumption.

The observations record literal JavaScript workloads and exact artifact/runner
provenance. They are offline measurements, not universal speedups or fitted runtime
selection evidence. No allocation-byte measurement is claimed. See the distribution's
`docs/composable-state-optimisation.md` for limits and the validation commands.
