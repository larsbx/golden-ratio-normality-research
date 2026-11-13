import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Count
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Simpa
import Lean.Elab.Tactic.Induction
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.Tactic.Congr
import Lean.Elab.Tactic.Split

/-!
# Exact contiguous-block counts

The empty pattern is assigned count zero. Every nonempty occurrence consumes
consecutive symbols and must fit completely inside the supplied word. The
implementation visits all starting positions, including overlapping matches.
-/

namespace GoldenNormality.Blocks

variable {α : Type} [DecidableEq α]

/-- A nonempty pattern occurs at the beginning of this suffix. -/
def occurs (pattern text : List α) : Bool :=
  decide (pattern ≠ [] ∧ text.take pattern.length = pattern)

/-- Count consecutive occurrences, advancing the starting position by one. -/
def count (pattern : List α) : List α → Nat
  | [] => 0
  | a :: rest => count pattern rest + if occurs pattern (a :: rest) then 1 else 0

/-- Independent specification: inspect every integer starting position. -/
def enumeratedCount (pattern text : List α) : Nat :=
  (List.range text.length).countP (fun i => occurs pattern (text.drop i))

theorem count_eq_enumerated (pattern text : List α) :
    count pattern text = enumeratedCount pattern text := by
  induction text with
  | nil => simp [count, enumeratedCount]
  | cons a rest ih =>
    simpa [count, enumeratedCount, List.range_succ_eq_map, List.countP_cons,
      List.countP_map, Function.comp_def] using ih

theorem occurs_iff (pattern text : List α) :
    occurs pattern text = true ↔ pattern ≠ [] ∧ text.take pattern.length = pattern := by
  simp [occurs]

/-- A reported occurrence necessarily fits within the available suffix. -/
theorem occurs_fits {pattern text : List α} (h : occurs pattern text = true) :
    pattern.length ≤ text.length := by
  have he := (occurs_iff pattern text).mp h
  have hl := congrArg List.length he.2
  simp only [List.length_take] at hl
  omega

theorem count_empty_pattern (text : List α) : count ([] : List α) text = 0 := by
  induction text with
  | nil => rfl
  | cons a rest ih => simp [count, occurs, ih]

/-- The suffix is too short alone but a match is completed by the right word.
`cross` evaluates this predicate only on nonempty suffixes of the left word. -/
def crossingAt (pattern left right : List α) : Bool :=
  decide (left.length < pattern.length) && occurs pattern (left ++ right)

/-- Sum the crossing predicate over starting positions in the left word. -/
def cross (pattern : List α) : List α → List α → Nat
  | [], _ => 0
  | a :: rest, right => cross pattern rest right +
      if crossingAt pattern (a :: rest) right then 1 else 0

theorem crossingAt_iff (pattern left right : List α) :
    crossingAt pattern left right = true ↔
      left.length < pattern.length ∧ pattern ≠ [] ∧
      (left ++ right).take pattern.length = pattern := by
  simp [crossingAt, occurs]

theorem occurs_append_of_fits (pattern left right : List α)
    (h : pattern.length ≤ left.length) :
    occurs pattern (left ++ right) = occurs pattern left := by
  simp [occurs, List.take_append_of_le_length h]

theorem occurs_false_of_short (pattern text : List α)
    (h : text.length < pattern.length) : occurs pattern text = false := by
  cases he : occurs pattern text with
  | false => rfl
  | true => have hf := occurs_fits he; omega

theorem occurrence_split (pattern left right : List α) :
    (if occurs pattern (left ++ right) then 1 else 0) =
      (if occurs pattern left then 1 else 0) +
      (if crossingAt pattern left right then 1 else 0) := by
  by_cases h : pattern.length ≤ left.length
  · have hn : ¬left.length < pattern.length := by omega
    simp [crossingAt, hn, occurs_append_of_fits pattern left right h]
  · have hs : left.length < pattern.length := by omega
    simp [crossingAt, hs, occurs_false_of_short pattern left hs]

/-- Exact chunk composition, retaining every match crossing the join. -/
theorem count_append (pattern left right : List α) :
    count pattern (left ++ right) =
      count pattern left + count pattern right + cross pattern left right := by
  induction left with
  | nil => simp [count, cross]
  | cons a rest ih =>
    have hs := occurrence_split pattern (a :: rest) right
    simp only [List.cons_append] at hs
    simp only [List.cons_append, count, cross]
    rw [ih, hs]
    omega

/-- Independent specification for the boundary term. -/
def enumeratedCross (pattern left right : List α) : Nat :=
  (List.range left.length).countP
    (fun i => crossingAt pattern (left.drop i) right)

theorem cross_eq_enumerated (pattern left right : List α) :
    cross pattern left right = enumeratedCross pattern left right := by
  induction left with
  | nil => simp [cross, enumeratedCross]
  | cons a rest ih =>
    simpa [cross, enumeratedCross, List.range_succ_eq_map, List.countP_cons,
      List.countP_map, Function.comp_def] using ih

omit [DecidableEq α] in
/-- Reading a nonempty left suffix needs at most `k - 1` symbols on the right. -/
theorem take_append_take_boundary (pattern left right : List α) (hl : left ≠ []) :
    (left ++ right.take (pattern.length - 1)).take pattern.length =
      (left ++ right).take pattern.length := by
  have hpos : 0 < left.length := List.length_pos_iff.mpr hl
  have h : pattern.length - left.length ≤ pattern.length - 1 := by omega
  simp [List.take_append, List.take_take, Nat.min_eq_left h]

theorem cross_take_right (pattern left right : List α) :
    cross pattern left (right.take (pattern.length - 1)) = cross pattern left right := by
  induction left with
  | nil => rfl
  | cons a rest ih =>
    have ht := take_append_take_boundary pattern (a :: rest) right (by simp)
    simp only [List.cons_append] at ht
    simp only [cross, ih]
    congr 1
    simp only [crossingAt, occurs, List.cons_append, ht]
    rfl

/-- Starts earlier than the last `k - 1` left symbols cannot cross the join. -/
theorem cross_drop_left (pattern left right : List α) :
    cross pattern left right =
      cross pattern (left.drop (left.length - (pattern.length - 1))) right := by
  induction left with
  | nil => simp [cross]
  | cons a rest ih =>
    by_cases h : (a :: rest).length < pattern.length
    · have hz : (a :: rest).length - (pattern.length - 1) = 0 := by omega
      rw [hz, List.drop_zero]
    · have hd : (a :: rest).length - (pattern.length - 1) =
          (rest.length - (pattern.length - 1)) + 1 := by
        simp only [List.length_cons] at *
        omega
      rw [hd, List.drop_succ_cons]
      simpa only [cross, crossingAt, h, decide_false, Bool.false_and,
        Bool.false_eq_true, ite_false, Nat.add_zero] using ih

/-- A boundary-only computation using at most `k - 1` symbols from each chunk. -/
def boundaryCount (pattern left right : List α) : Nat :=
  cross pattern
    (left.drop (left.length - (pattern.length - 1)))
    (right.take (pattern.length - 1))

theorem boundaryCount_eq_cross (pattern left right : List α) :
    boundaryCount pattern left right = cross pattern left right := by
  unfold boundaryCount
  rw [cross_take_right]
  exact (cross_drop_left pattern left right).symm

theorem count_append_boundary (pattern left right : List α) :
    count pattern (left ++ right) =
      count pattern left + count pattern right + boundaryCount pattern left right := by
  rw [boundaryCount_eq_cross]
  exact count_append pattern left right

theorem count_le_length (pattern text : List α) : count pattern text ≤ text.length := by
  induction text with
  | nil => simp [count]
  | cons a rest ih =>
    simp only [count, List.length_cons]
    split <;> omega

end GoldenNormality.Blocks
