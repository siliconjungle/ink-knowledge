import Std
import Lean.Elab.Tactic.Omega

namespace SharedSpine

-- Live nodes retain an edge; an absent edge is private destruction state.
inductive Spine (α : Type) where
  | empty
  | node (value : α) (tail : Option (Spine α))

def encode {α : Type} : List α → Spine α
  | [] => .empty
  | x :: xs => .node x (some (encode xs))

def decode {α : Type} : Spine α → Option (List α)
  | .empty => some []
  | .node _ none => none
  | .node x (some xs) => (decode xs).map (x :: ·)

theorem roundtrip {α : Type} (xs : List α) : decode (encode xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, decode, ih]

def detach {α : Type} : Spine α → Spine α × Option (Spine α)
  | .empty => (.empty, none)
  | .node x tail => (.node x none, tail)

theorem detach_once {α : Type} (s : Spine α) : (detach (detach s).1).2 = none := by
  cases s <;> rfl

theorem detached_tail_preserves_values {α : Type} (x : α) (xs : List α) :
    decode ((detach (encode (x :: xs))).2.getD .empty) = some xs := by
  exact roundtrip xs

-- A release of one root owner follows uniquely owned edges. At a shared
-- suffix it decrements the owner count and stops. Node labels model payloads;
-- this model assumes valid acyclic edges and accurate reference counts.
def release {α : Type} : List (α × Nat) → List (α × Nat)
  | [] => []
  | (x, n) :: xs => if n = 1 then release xs else (x, n - 1) :: xs

def freed {α : Type} : List (α × Nat) → List α
  | [] => []
  | (x, n) :: xs => if n = 1 then x :: freed xs else []

theorem payload_partition {α : Type} (xs : List (α × Nat)) :
    xs.map Prod.fst = freed xs ++ (release xs).map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons entry xs ih =>
    rcases entry with ⟨x, n⟩
    by_cases unique : n = 1
    · simp [freed, release, unique, ih]
    · simp [freed, release, unique]

theorem shared_suffix_untouched {α : Type} (uniqueNodes : List α)
    (x : α) (owners : Nat) (tail : List (α × Nat)) (shared : 1 < owners) :
    release (uniqueNodes.map (fun a => (a, 1)) ++ (x, owners) :: tail) =
      (x, owners - 1) :: tail := by
  induction uniqueNodes with
  | nil => simp [release, Nat.ne_of_gt shared]
  | cons a uniqueNodes ih => simpa [release] using ih

theorem surviving_owners_positive {α : Type} (xs : List (α × Nat))
    (valid : ∀ entry ∈ xs, 0 < entry.2) :
    ∀ entry ∈ release xs, 0 < entry.2 := by
  induction xs with
  | nil => simp [release]
  | cons pair xs ih =>
    rcases pair with ⟨x, n⟩
    have positive : 0 < n := valid (x, n) (by simp)
    have rest : ∀ entry ∈ xs, 0 < entry.2 := by
      intro entry h
      exact valid entry (by simp [h])
    by_cases unique : n = 1
    · simpa [release, unique] using ih rest
    · intro entry h
      simp [release, unique] at h
      rcases h with h | h
      · subst entry
        omega
      · exact rest entry h

-- No replacement node is created by detach/release. This is an allocation
-- model of those operations, not a proof of Rust's allocator or Arc library.
def replacementAllocations {α : Type} : List (α × Nat) → Nat
  | [] => 0
  | (_, n) :: xs => if n = 1 then replacementAllocations xs else 0

theorem release_allocates_no_replacements {α : Type} (xs : List (α × Nat)) :
    replacementAllocations xs = 0 := by
  induction xs with
  | nil => rfl
  | cons pair xs ih =>
    rcases pair with ⟨x, n⟩
    by_cases h : n = 1 <;> simp [replacementAllocations, h, ih]

end SharedSpine
#print axioms SharedSpine.roundtrip
#print axioms SharedSpine.shared_suffix_untouched
#print axioms SharedSpine.surviving_owners_positive
#print axioms SharedSpine.release_allocates_no_replacements
