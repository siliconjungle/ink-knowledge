namespace InkSignedDeltas

def total {α : Type} (f : α → Int) : List (α × Int) → Int
  | [] => 0
  | (x, w) :: xs => total f xs + w * f x

def negate {α : Type} (xs : List (α × Int)) : List (α × Int) :=
  xs.map (fun e => (e.1, -e.2))

theorem total_append {α : Type} (f : α → Int) (xs ys : List (α × Int)) :
    total f (xs ++ ys) = total f ys + total f xs := by
  induction xs with
  | nil => simp [total]
  | cons e xs ih =>
    obtain ⟨x, w⟩ := e
    simp only [List.cons_append, total, ih]
    omega

theorem total_negate {α : Type} (f : α → Int) (xs : List (α × Int)) :
    total f (negate xs) = - total f xs := by
  induction xs with
  | nil => simp [negate, total]
  | cons e xs ih =>
    obtain ⟨x, w⟩ := e
    simp only [negate, List.map_cons, total] at ih ⊢
    rw [ih, Int.neg_mul]
    omega

theorem retraction_cancels {α : Type} (f : α → Int) (xs : List (α × Int)) :
    total f (xs ++ negate xs) = 0 := by
  rw [total_append, total_negate]
  omega

theorem signed_replacement {α : Type} (f : α → Int) (xs : List (α × Int)) (old new : α) :
    total f (xs ++ [(old, -1), (new, 1)]) = total f xs - f old + f new := by
  rw [total_append]
  simp only [total]
  rw [Int.neg_one_mul, Int.one_mul]
  omega

theorem total_insert_anywhere {α : Type} (f : α → Int) (pre post : List (α × Int)) (e : α × Int) :
    total f (pre ++ e :: post) = total f (pre ++ post) + e.2 * f e.1 := by
  rw [total_append, total_append]
  obtain ⟨x, w⟩ := e
  simp only [total]
  omega

end InkSignedDeltas
