import Std

namespace IndexedUndo

variable {K V : Type} [DecidableEq K]
abbrev Table (K V : Type) := K → Option V
abbrev Entry (K V : Type) := K × Option V

def set (table : Table K V) (key : K) (value : Option V) : Table K V :=
  fun query => if query = key then value else table query

-- Record the preceding value for each write. None records prior absence.
def write (table : Table K V) (journal : List (Entry K V)) (key : K)
    (value : Option V) : Table K V × List (Entry K V) :=
  (set table key value, (key, table key) :: journal)

def rollback (table : Table K V) : List (Entry K V) → Table K V
  | [] => table
  | (key, old) :: rest => rollback (set table key old) rest

theorem restore_write (table : Table K V) (key : K) (value : Option V) :
    set (set table key value) key (table key) = table := by
  funext query
  by_cases h : query = key
  · subst query; simp [set]
  · simp [set, h]

theorem rollback_write (table : Table K V) (journal : List (Entry K V))
    (key : K) (value : Option V) :
    rollback (write table journal key value).1 (write table journal key value).2 =
      rollback table journal := by
  simp only [write, rollback, restore_write]

def run (table : Table K V) (journal : List (Entry K V)) :
    List (Entry K V) → Table K V × List (Entry K V)
  | [] => (table, journal)
  | (key, value) :: rest =>
      let next := write table journal key value
      run next.1 next.2 rest

-- Covers repeated keys, inserts, replacements, deletes and writes to several
-- roots (K can be a root/key pair). Nested changes share one outer journal.
theorem rollback_history (table : Table K V) (journal writes : List (Entry K V)) :
    rollback (run table journal writes).1 (run table journal writes).2 =
      rollback table journal := by
  induction writes generalizing table journal with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [run]
    rw [ih, rollback_write]

theorem abort_restores_all_rows (table : Table K V) (writes : List (Entry K V)) :
    rollback (run table [] writes).1 (run table [] writes).2 = table := by
  simpa [rollback] using rollback_history table [] writes

-- Commit discards the journal while keeping the final table. Domain failure,
-- host failure and exhausted commit sequence all use the same rollback branch.
def finish (initial : Table K V) (writes : List (Entry K V)) (commit : Bool) : Table K V :=
  let next := run initial [] writes
  if commit then next.1 else rollback next.1 next.2

theorem failed_change_restores (table : Table K V) (writes : List (Entry K V)) :
    finish table writes false = table := abort_restores_all_rows table writes

theorem committed_change_keeps_result (table : Table K V) (writes : List (Entry K V)) :
    finish table writes true = (run table [] writes).1 := rfl

end IndexedUndo
#print axioms IndexedUndo.abort_restores_all_rows
#print axioms IndexedUndo.failed_change_restores
