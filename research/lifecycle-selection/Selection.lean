import Std
import Lean.Elab.Tactic.Omega

namespace LifecycleSelection

-- Costs are scaled to a common denominator (medians in the planner are exact
-- Fractions). Values describe measured work, not bounds on future execution.
structure Costs where
  setup : Nat
  query : Nat
  update : Nat
  switch : Nat

def total (c : Costs) (queries updates switches : Nat) : Nat :=
  c.setup + queries * c.query + updates * c.update + switches * c.switch

-- A cache with expensive indexed/list maintenance pays only when its saved
-- query work exceeds setup, update and migration differences.
theorem break_even (base cache : Costs) (queries updates switches : Nat) :
    total cache queries updates switches < total base queries updates switches ↔
      cache.setup + queries * cache.query + updates * cache.update + switches * cache.switch <
      base.setup + queries * base.query + updates * base.update + switches * base.switch := Iff.rfl

theorem query_savings_pay_for_maintenance (base cache : Costs)
    (queries updates switches setupExtra updateExtra switchExtra saving : Nat)
    (hs : cache.setup = base.setup + setupExtra)
    (hu : cache.update = base.update + updateExtra)
    (hm : cache.switch = base.switch + switchExtra)
    (hq : base.query = cache.query + saving) :
    total cache queries updates switches < total base queries updates switches ↔
      setupExtra + updates * updateExtra + switches * switchExtra < queries * saving := by
  simp only [total, hs, hu, hm, hq, Nat.mul_add]
  omega

-- Missing comparable measurements cannot authorize a profitable switch.
def consider (cost : α → Nat) (_baseline best : α) (candidate : α × Bool) : α :=
  if candidate.2 && decide (cost candidate.1 < cost best) then candidate.1 else best

def choose (cost : α → Nat) (baseline : α) (comparable : Bool)
    (candidates : List (α × Bool)) : α :=
  if comparable then candidates.foldl (consider cost baseline) baseline else baseline

theorem missing_baseline_keeps_baseline (cost : α → Nat) (baseline : α)
    (candidates : List (α × Bool)) : choose cost baseline false candidates = baseline := rfl

theorem consider_never_worsens (cost : α → Nat) (baseline best : α)
    (candidate : α × Bool) :
    cost (consider cost baseline best candidate) ≤ cost best := by
  unfold consider
  split
  · rename_i h
    have cheaper : cost candidate.1 < cost best := by
      cases eligible : candidate.2 <;> simp [eligible] at h
      exact h
    omega
  · exact Nat.le_refl _

theorem fold_never_worsens (cost : α → Nat) (baseline best : α)
    (candidates : List (α × Bool)) :
    cost (candidates.foldl (consider cost baseline) best) ≤ cost best := by
  induction candidates generalizing best with
  | nil => exact Nat.le_refl _
  | cons candidate rest ih =>
    exact Nat.le_trans (ih _) (consider_never_worsens cost baseline best candidate)

theorem measured_choice_never_worsens (cost : α → Nat) (baseline : α)
    (comparable : Bool) (candidates : List (α × Bool)) :
    cost (choose cost baseline comparable candidates) ≤ cost baseline := by
  cases comparable with
  | false => exact Nat.le_refl _
  | true => exact fold_never_worsens cost baseline baseline candidates

-- Each eligible candidate is no cheaper than the fold's current winner.
theorem consider_covers_candidate (cost : α → Nat) (baseline best candidate : α) :
    cost (consider cost baseline best (candidate, true)) ≤ cost candidate := by
  unfold consider
  split
  · exact Nat.le_refl _
  · rename_i h
    have not_cheaper : ¬ cost candidate < cost best := by simpa using h
    omega

theorem fold_covers_candidates (cost : α → Nat) (baseline best : α)
    (candidates : List (α × Bool)) (candidate : α)
    (member : (candidate, true) ∈ candidates) :
    cost (candidates.foldl (consider cost baseline) best) ≤ cost candidate := by
  induction candidates generalizing best with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.mem_cons] at member
    rcases member with same | later
    · subst head
      exact Nat.le_trans (fold_never_worsens cost baseline _ rest)
        (consider_covers_candidate cost baseline best candidate)
    · exact ih _ later

-- Strict improvement keeps the baseline on ties and forbids an unmeasured
-- candidate from replacing it. Eligibility represents complete comparable phases.
theorem unmeasured_ignored (cost : α → Nat) (baseline best candidate : α) :
    consider cost baseline best (candidate, false) = best := by simp [consider]

theorem tie_keeps_current (cost : α → Nat) (baseline best candidate : α)
    (tie : cost candidate = cost best) :
    consider cost baseline best (candidate, true) = best := by simp [consider, tie]

end LifecycleSelection
#print axioms LifecycleSelection.measured_choice_never_worsens
#print axioms LifecycleSelection.fold_covers_candidates
