namespace InkIncrementalViews

def sumInts : List Int → Int
  | [] => 0
  | x :: xs => sumInts xs + x

def countList {α : Type} : List α → Int
  | [] => 0
  | _ :: xs => countList xs + 1

theorem sum_append (xs ys : List Int) :
    sumInts (xs ++ ys) = sumInts ys + sumInts xs := by
  induction xs with
  | nil => simp [sumInts]
  | cons x xs ih => simp only [List.cons_append, sumInts, ih]; omega

theorem sum_append_commutes (xs ys : List Int) :
    sumInts (xs ++ ys) = sumInts (ys ++ xs) := by
  rw [sum_append, sum_append]; omega

theorem count_append {α : Type} (xs ys : List α) :
    countList (xs ++ ys) = countList ys + countList xs := by
  induction xs with
  | nil => simp [countList]
  | cons x xs ih => simp only [List.cons_append, countList, ih]; omega

theorem map_append_linear {α β : Type} (f : α → β) (xs ys : List α) :
    (xs ++ ys).map f = xs.map f ++ ys.map f := by
  simp

theorem filter_append_linear {α : Type} (p : α → Bool) (xs ys : List α) :
    (xs ++ ys).filter p = xs.filter p ++ ys.filter p := by
  simp

theorem sum_map_append {α : Type} (f : α → Int) (xs ys : List α) :
    sumInts ((xs ++ ys).map f) = sumInts (ys.map f) + sumInts (xs.map f) := by
  rw [map_append_linear, sum_append]

theorem count_filter_append {α : Type} (p : α → Bool) (xs ys : List α) :
    countList ((xs ++ ys).filter p) = countList (ys.filter p) + countList (xs.filter p) := by
  rw [filter_append_linear, count_append]

theorem addition_interchange (a b c d : Int) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  omega

theorem decompose_filter_map {α : Type} (p : α → Bool) (f : α → Int) (rows : List α) :
    sumInts ((rows.filter p).map f) = sumInts (rows.map (fun r => if p r then f r else 0)) := by
  induction rows with
  | nil => simp [sumInts]
  | cons r rs ih =>
    cases h : p r <;> simp [List.filter, h, sumInts, ih]

theorem decompose_map_filter {α β : Type} (f : α → β) (p : β → Bool) (g : β → Int) (rows : List α) :
    sumInts (((rows.map f).filter p).map g) =
      sumInts (rows.map (fun r => if p (f r) then g (f r) else 0)) := by
  rw [decompose_filter_map, List.map_map]
  rfl

theorem decompose_count_filter {α : Type} (p : α → Bool) (rows : List α) :
    countList (rows.filter p) = sumInts (rows.map (fun r => if p r then 1 else 0)) := by
  induction rows with
  | nil => simp [countList, sumInts]
  | cons r rs ih =>
    cases h : p r <;> simp [List.filter, h, countList, sumInts, ih]

structure KeyedRow where
  key : UInt64
  value : Int

def joinMatches (key : UInt64) (value : Int) : List KeyedRow → Int
  | [] => 0
  | r :: rs => joinMatches key value rs + (if key = r.key then value + r.value else 0)

def joinSum : List KeyedRow → List KeyedRow → Int
  | [], _ => 0
  | r :: rs, bs => joinSum rs bs + joinMatches r.key r.value bs

theorem join_matches_append (key : UInt64) (value : Int) (bs db : List KeyedRow) :
    joinMatches key value (bs ++ db) = joinMatches key value db + joinMatches key value bs := by
  induction bs with
  | nil => simp [joinMatches]
  | cons r rs ih => simp only [List.cons_append, joinMatches, ih]; omega

theorem join_left_append (as da bs : List KeyedRow) :
    joinSum (as ++ da) bs = joinSum da bs + joinSum as bs := by
  induction as with
  | nil => simp [joinSum]
  | cons r rs ih => simp only [List.cons_append, joinSum, ih]; omega

theorem join_right_append (as bs db : List KeyedRow) :
    joinSum as (bs ++ db) = joinSum as db + joinSum as bs := by
  induction as with
  | nil => simp [joinSum]
  | cons r rs ih => simp only [joinSum, ih, join_matches_append]; omega

theorem join_delta (as da bs db : List KeyedRow) :
    joinSum (as ++ da) (bs ++ db) =
      (joinSum da db + joinSum da bs) + (joinSum as db + joinSum as bs) := by
  rw [join_left_append, join_right_append, join_right_append]

end InkIncrementalViews
