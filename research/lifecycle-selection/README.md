# Lifecycle selection model

`Selection.lean` models the external planner's strict improvement fold over
candidates with complete comparable measurements. It proves baseline retention
when baseline evidence is absent, rejection of unmeasured candidates, tie
retention, no increase in the supplied lifecycle cost, and minimum supplied cost
among eligible candidates. It also proves the amortization inequality: saved
query work must exceed additional setup, update and migration work.

Costs use natural numbers scaled to a common denominator. The Python planner
uses exact rational medians; all medians have denominators dividing two, so this
scaling preserves comparisons. Phase completeness, target/workload provenance,
memory constraints and migration evidence determine eligibility outside this
model. These are measured estimates, not bounds on future time or memory.

No new axioms or `sorry` are used. The model does not verify Python/Rust compiler
implementations, measurement acquisition, generated machine code or table
algorithms. Source checking and representation checking separately establish
which implementations can enter selection; low cost never grants correctness.

The distribution's mandatory `point_delta` suite runs the independent Lean
checker when `INK_TEST_LEAN` is supplied and requires it in complete parity mode.
The external planner compares database candidate IDs uniformly; an ordinary
implementation is an empty checked-selection package. Its replay tool binds exact
source, compiler bytes, emission lane and pinned database package, then invokes
the existing proof checker and emitter. No algorithm choice is added to core.

`Undo.lean` models indexed table writes and their inverse journal. It proves
that reverse replay restores the original mapping for arbitrary histories,
including repeated keys and several roots, and that commit keeps the final
mapping. Domain errors, host errors and commit exhaustion use that same abort
branch. It assumes stored payloads retain their value, as enforced by Ink's
immutable row semantics; it does not certify a mutable foreign row object.
The executable reference/parity fixtures check replies, rollback, version,
ordered events and exact portable snapshots separately from this table model.
