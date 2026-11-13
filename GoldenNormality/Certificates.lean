import GoldenNormality.Prefix
import GoldenNormality.Blocks

/-!
# Binding finite native words to the actual digits

`DigitsAt` is a proposition about the real-number digit function from `Prefix`.
It is not a label attached to a native transcript.  A finite consumer must prove
every conjunct, for example from adjacent integer prefix certificates.
-/

namespace GoldenNormality

/-- Every supplied symbol equals the actual digit at the stated starting position. -/
def DigitsAt (b start : ℕ) : List ℕ → Prop
  | [] => True
  | d :: rest => digit b start = (d : ℤ) ∧ DigitsAt b (start + 1) rest

@[simp] theorem digitsAt_nil (b start : ℕ) : DigitsAt b start [] := trivial

@[simp] theorem digitsAt_cons_iff (b start d : ℕ) (rest : List ℕ) :
    DigitsAt b start (d :: rest) ↔
      digit b start = (d : ℤ) ∧ DigitsAt b (start + 1) rest := Iff.rfl

theorem digitsAt_getElem {b start : ℕ} {text : List ℕ}
    (h : DigitsAt b start text) (i : ℕ) (hi : i < text.length) :
    digit b (start + i) = (text[i] : ℤ) := by
  induction text generalizing start i with
  | nil => simp at hi
  | cons d rest ih =>
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < rest.length := by simpa using hi
      have he : start + i.succ = (start + 1) + i := by omega
      simpa only [List.getElem_cons_succ, he] using ih h.2 i hi'

/-- The finite word obtained from the mathematical digit function. -/
noncomputable def actualDigits (b start length : ℕ) : List ℕ :=
  (List.range length).map (fun i => (digit b (start + i)).toNat)

@[simp] theorem actualDigits_length (b start length : ℕ) :
    (actualDigits b start length).length = length := by
  simp [actualDigits]

@[simp] theorem actualDigits_zero (b start : ℕ) : actualDigits b start 0 = [] := rfl

theorem actualDigits_succ (b start length : ℕ) :
    actualDigits b start (length + 1) =
      (digit b start).toNat :: actualDigits b (start + 1) length := by
  unfold actualDigits
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  congr 2
  omega

/-- A certified native word is exactly the indicated mathematical digit segment. -/
theorem digitsAt_eq_actualDigits {b start : ℕ} {text : List ℕ}
    (h : DigitsAt b start text) : text = actualDigits b start text.length := by
  induction text generalizing start with
  | nil => rfl
  | cons d rest ih =>
    rw [List.length_cons, actualDigits_succ, h.1]
    simp only [Int.toNat_natCast]
    exact congrArg (List.cons d) (ih h.2)

/-- Counter acceptance concerns the real digits once the word binding is proved. -/
theorem certified_count_eq_actual {b start : ℕ} {text : List ℕ}
    (h : DigitsAt b start text) (pattern : List ℕ) :
    Blocks.count pattern text =
      Blocks.enumeratedCount pattern (actualDigits b start text.length) := by
  rw [Blocks.count_eq_enumerated]
  exact congrArg (Blocks.enumeratedCount pattern) (digitsAt_eq_actualDigits h)

/-- An observed numeral count is promoted only after both independent equalities hold. -/
theorem certified_count_sound {b start value : ℕ} {text pattern : List ℕ}
    (digits : DigitsAt b start text) (count : Blocks.count pattern text = value) :
    Blocks.enumeratedCount pattern (actualDigits b start text.length) = value := by
  rw [← certified_count_eq_actual digits pattern]
  exact count

end GoldenNormality
