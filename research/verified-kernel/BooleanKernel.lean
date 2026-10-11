-- Independent Boolean equality kernel. No added axioms, sorry, or native_decide.
namespace InkBoolean
inductive Op where
  | and | or | eq | ne
  deriving DecidableEq
inductive Term where
  | var : Nat → Term
  | lit : Bool → Term
  | bin : Op → Term → Term → Term
  deriving DecidableEq
abbrev Env := Nat → Bool
def apply : Op → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or, a, b => a || b
  | .eq, a, b => a == b
  | .ne, a, b => a != b
def eval (ρ : Env) : Term → Bool
  | .var i => ρ i
  | .lit b => b
  | .bin o a b => apply o (eval ρ a) (eval ρ b)
def subst (i : Nat) (b : Bool) : Term → Term
  | .var j => if j = i then .lit b else .var j
  | .lit v => .lit v
  | .bin o x y => .bin o (subst i b x) (subst i b y)
def set (ρ : Env) (i : Nat) (b : Bool) : Env := fun j => if j = i then b else ρ j
 theorem eval_subst (ρ : Env) (i : Nat) (b : Bool) (t : Term) :
    eval ρ (subst i b t) = eval (set ρ i b) t := by
  induction t with
  | var j => simp [subst, eval, set]; split <;> simp_all [eval]
  | lit v => rfl
  | bin o x y hx hy => simp [subst, eval, hx, hy]
 theorem set_same (ρ : Env) (i : Nat) : set ρ i (ρ i) = ρ := by
  funext j; by_cases h : j = i <;> simp [set, h]
abbrev Context := List (Term × Term)
def Valid (Γ : Context) (ρ : Env) := ∀ a b, (a,b) ∈ Γ → eval ρ a = eval ρ b
 def subContext (Γ : Context) (i : Nat) (b : Bool) := Γ.map fun (a,c) => (subst i b a,subst i b c)
 theorem valid_sub (Γ : Context) (ρ : Env) (i : Nat) (b : Bool)
    (h : Valid Γ (set ρ i b)) : Valid (subContext Γ i b) ρ := by
  intro a c ha
  obtain ⟨⟨x,y⟩,hm,he⟩ := List.mem_map.mp ha
  cases he
  simpa [eval_subst] using h x y hm
 def closed : Term → Bool
  | .var _ => false
  | .lit _ => true
  | .bin _ a b => closed a && closed b
 theorem eval_closed (t : Term) (h : closed t = true) (ρ σ : Env) : eval ρ t = eval σ t := by
  induction t with
  | var i => simp [closed] at h
  | lit v => rfl
  | bin o a b ha hb =>
    have hs := Bool.and_eq_true_iff.mp h
    simp [eval, ha hs.1, hb hs.2]
-- Elaboration of these constructors is the independent certificate check.
-- Every imported premise is explicit; a closed theorem uses the empty context.
inductive Derives : Context → Term → Term → Prop where
  | refl : Derives Γ a a
  | hyp : (a,b) ∈ Γ → Derives Γ a b
  | sym : Derives Γ a b → Derives Γ b a
  | trans : Derives Γ a b → Derives Γ b c → Derives Γ a c
  | binary : Derives Γ a a' → Derives Γ b b' → Derives Γ (.bin o a b) (.bin o a' b')
  | compute : closed a = true → closed b = true → eval (fun _ => false) a = eval (fun _ => false) b → Derives Γ a b
  | cases : Derives (subContext Γ i false) (subst i false a) (subst i false b) →
            Derives (subContext Γ i true) (subst i true a) (subst i true b) → Derives Γ a b
  | shortAnd : Derives Γ a a' → Derives ((a,.lit true)::Γ) b b' → Derives Γ (.bin .and a b) (.bin .and a' b')
  | shortOr : Derives Γ a a' → Derives ((a,.lit false)::Γ) b b' → Derives Γ (.bin .or a b) (.bin .or a' b')
 theorem sound (h : Derives Γ a b) : ∀ ρ, Valid Γ ρ → eval ρ a = eval ρ b := by
  induction h with
  | refl => intro ρ hv; rfl
  | hyp hm => intro ρ hv; exact hv _ _ hm
  | sym h ih => intro ρ hv; exact (ih ρ hv).symm
  | trans h k ih ik => intro ρ hv; exact (ih ρ hv).trans (ik ρ hv)
  | binary h k ih ik => intro ρ hv; simp [eval, ih ρ hv, ik ρ hv]
  | compute ha hb he => intro ρ hv; exact (eval_closed _ ha ρ _).trans (he.trans (eval_closed _ hb _ ρ))
  | @cases Γ i a b hf ht ihf iht =>
    intro ρ hv
    cases he : ρ i with
    | false =>
      have hs : set ρ i false = ρ := by rw [← he]; exact set_same ρ i
      have hh := ihf ρ (valid_sub Γ ρ i false (by simpa [hs] using hv))
      simpa [eval_subst, hs] using hh
    | true =>
      have hs : set ρ i true = ρ := by rw [← he]; exact set_same ρ i
      have hh := iht ρ (valid_sub Γ ρ i true (by simpa [hs] using hv))
      simpa [eval_subst, hs] using hh
  | @shortAnd Γ a a' b b' h k ih ik =>
    intro ρ hv
    have hl := ih ρ hv
    cases he : eval ρ a with
    | false => simp [eval, apply, ← hl, he]
    | true =>
      have hr := ik ρ (by intro x y hm; rcases List.mem_cons.mp hm with hxy | hxy; cases hxy; exact he; exact hv x y hxy)
      simp [eval, apply, ← hl, he, hr]
  | @shortOr Γ a a' b b' h k ih ik =>
    intro ρ hv
    have hl := ih ρ hv
    cases he : eval ρ a with
    | true => simp [eval, apply, ← hl, he]
    | false =>
      have hr := ik ρ (by intro x y hm; rcases List.mem_cons.mp hm with hxy | hxy; cases hxy; exact he; exact hv x y hxy)
      simp [eval, apply, ← hl, he, hr]
 theorem closed_sound (h : Derives [] a b) : ∀ ρ, eval ρ a = eval ρ b := by
  intro ρ; exact sound h ρ (by intro x y hm; simp at hm)
#print axioms sound
#print axioms closed_sound
end InkBoolean
