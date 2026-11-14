import GoldenNormality.BinaryComplement
import GoldenNormality.Normality
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Complementary words and occurrence counts

The words below are defined from the real digits of `beta`. Their equality to
the complemented power evaluator is proved, as is the exact count transfer for
every fixed-width block. The value map keeps its width and alphabet bound;
leading zeros and overlapping starting positions are retained.

The final equivalence transfers the open binary normality proposition. It
does not prove either side of that equivalence.
-/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

/-- Complement a numeral within a fixed binary width. The valid range is
`j < 2^length`; natural subtraction alone does not enforce that precondition. -/
def flipValue (length j : ℕ) : ℕ := 2 ^ length - 1 - j

theorem flipValue_lt {length j : ℕ} (hj : j < 2 ^ length) :
    flipValue length j < 2 ^ length := by
  unfold flipValue
  omega

theorem flipValue_involutive {length j : ℕ} (hj : j < 2 ^ length) :
    flipValue length (flipValue length j) = j := by
  unfold flipValue
  omega

/-- An actual complementary block is matched to the original block at the
same start and width. -/
theorem blockValue_eq_iff {start length j : ℕ} (hj : j < 2 ^ length) :
    blockValue start length = (j : ℤ) ↔
      GoldenNormality.blockValue 2 start length = (flipValue length j : ℤ) := by
  have hsum : j + flipValue length j + 1 = 2 ^ length := by
    unfold flipValue
    omega
  have hsum' : (j : ℤ) + (flipValue length j : ℤ) + 1 = (2 : ℤ) ^ length := by
    exact_mod_cast hsum
  rw [blockValue_eq_complement]
  omega

/-- The complementary word is defined from its real-number digit function. -/
noncomputable def actualDigits (start length : ℕ) : List ℕ :=
  (List.range length).map (fun i => (digit (start + i)).toNat)

@[simp] theorem actualDigits_length (start length : ℕ) :
    (actualDigits start length).length = length := by
  simp [actualDigits]

theorem actualDigits_eq_map (start length : ℕ) :
    actualDigits start length =
      (GoldenNormality.actualDigits 2 start length).map (fun d => 1 - d) := by
  simp only [actualDigits, GoldenNormality.actualDigits, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro i _
  have h := GoldenNormality.digit_range (by decide : 0 < 2) (start + i)
  rw [digit_eq_complement]
  omega

theorem actualDigits_inAlphabet (start length : ℕ) :
    InAlphabet 2 (actualDigits start length) := by
  rw [actualDigits_eq_map]
  have h := GoldenNormality.actualDigits_inAlphabet (by decide : 0 < 2) start length
  generalize GoldenNormality.actualDigits 2 start length = word at *
  induction word with
  | nil => trivial
  | cons d rest ih =>
    change 1 - d < 2 ∧ InAlphabet 2 (rest.map (fun d => 1 - d))
    exact ⟨by omega, ih h.2⟩

private theorem numeral_complement {word : List ℕ} (h : InAlphabet 2 word) :
    wordValue 2 (word.map (fun d => 1 - d)) + wordValue 2 word + 1 =
      2 ^ word.length := by
  induction word with
  | nil => simp [wordValue]
  | cons d rest ih =>
    have ht := ih h.2
    have hd : 1 - d + d = 1 := by have := h.1; omega
    have hm := congrArg (fun x : ℕ => x * 2 ^ rest.length) hd
    simp only [List.map_cons, wordValue, List.length_map, List.length_cons, pow_succ]
    nlinarith

theorem wordValue_actualDigits (start length : ℕ) :
    (wordValue 2 (actualDigits start length) : ℤ) = blockValue start length := by
  have hn := numeral_complement
    (GoldenNormality.actualDigits_inAlphabet (by decide : 0 < 2) start length)
  rw [GoldenNormality.actualDigits_length] at hn
  have hn' :
      (wordValue 2 ((GoldenNormality.actualDigits 2 start length).map (fun d => 1 - d)) : ℤ) +
        (wordValue 2 (GoldenNormality.actualDigits 2 start length) : ℤ) + 1 =
          (2 : ℤ) ^ length := by exact_mod_cast hn
  rw [GoldenNormality.wordValue_actualDigits] at hn'
  rw [actualDigits_eq_map, blockValue_eq_complement]
  omega

/-- A computable complementary word obtained from the proved power evaluator. -/
def powerDigits (start length : ℕ) : List ℕ :=
  (BinaryAutomaton.powerDigits start length).map (fun d => 1 - d)

@[simp] theorem powerDigits_length (start length : ℕ) :
    (powerDigits start length).length = length := by
  simp [powerDigits]

theorem powerDigits_eq_actualDigits (start length : ℕ) :
    powerDigits start length = actualDigits start length := by
  rw [powerDigits, BinaryAutomaton.powerDigits_eq_actualDigits, actualDigits_eq_map]

theorem wordValue_powerDigits (start length : ℕ) :
    (wordValue 2 (powerDigits start length) : ℤ) = blockValue start length := by
  rw [powerDigits_eq_actualDigits, wordValue_actualDigits]

/-- Count all `N` starting positions of actual complementary blocks, retaining
overlaps. For positive `N,length`, this observes `N+length-1` digits. -/
noncomputable def occurrences (length j N : ℕ) : ℕ :=
  (List.range N).countP (fun n => decide (blockValue n length = (j : ℤ)))

@[simp] theorem occurrences_zero (length j : ℕ) : occurrences length j 0 = 0 := by
  simp [occurrences]

theorem occurrences_eq_complement {length j : ℕ} (hj : j < 2 ^ length) (N : ℕ) :
    occurrences length j N =
      GoldenNormality.occurrences 2 length (flipValue length j) N := by
  unfold occurrences GoldenNormality.occurrences
  congr 1
  funext n
  simp only [decide_eq_decide]
  exact blockValue_eq_iff (start := n) hj

theorem original_occurrences_eq_complement {length j : ℕ} (hj : j < 2 ^ length)
    (N : ℕ) :
    GoldenNormality.occurrences 2 length j N =
      occurrences length (flipValue length j) N := by
  rw [occurrences_eq_complement (flipValue_lt hj), flipValue_involutive hj]

theorem ones_eq_original_zeros (N : ℕ) :
    occurrences 1 1 N = GoldenNormality.occurrences 2 1 0 N := by
  simpa [flipValue] using occurrences_eq_complement (j := 1) (length := 1) (by decide) N

theorem zeros_eq_original_ones (N : ℕ) :
    occurrences 1 0 N = GoldenNormality.occurrences 2 1 1 N := by
  simpa [flipValue] using occurrences_eq_complement (j := 0) (length := 1) (by decide) N

/-- The ordinary digit sum equals the actual one count; this makes finite
convolution bounds directly comparable with the original zero-count target. -/
theorem digit_sum_eq_ones (N : ℕ) :
    (∑ i ∈ Finset.range N, digit i) = (occurrences 1 1 N : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : occurrences 1 1 (N + 1) =
        occurrences 1 1 N + if digit N = 1 then 1 else 0 := by
      have hblock : blockValue N 1 = digit N := by
        simp only [blockValue, digit, pow_one]
      unfold occurrences
      rw [List.range_succ, List.countP_append, List.countP_singleton, hblock]
      simp
    rw [Finset.sum_range_succ, ih, hstep, Nat.cast_add]
    have hd : digit N = 0 ∨ digit N = 1 := by have := digit_range N; omega
    rcases hd with hd | hd <;> simp [hd]

theorem digit_sum_eq_original_zeros (N : ℕ) :
    (∑ i ∈ Finset.range N, digit i) = (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  rw [digit_sum_eq_ones, ones_eq_original_zeros]

/-- Binary normality for the actual complementary number, with the same
quantifier order and integer discrepancy as the original open target. -/
def Normal : Prop :=
  ∀ length : ℕ, 1 ≤ length → ∀ j : ℕ, j < 2 ^ length →
    ∀ T : ℕ, 1 ≤ T → ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      Nat.dist ((2 ^ length) * occurrences length j N) N * T ≤ N

theorem normal_iff_original : Normal ↔ GoldenNormality.NormalInBase 2 := by
  constructor
  · intro h
    refine ⟨by decide, ?_⟩
    intro length hlength j hj T hT
    obtain ⟨N0, hN0, hbound⟩ := h length hlength (flipValue length j) (flipValue_lt hj) T hT
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    rw [original_occurrences_eq_complement hj]
    exact hbound N hN
  · intro h length hlength j hj T hT
    obtain ⟨N0, hN0, hbound⟩ := h.2 length hlength (flipValue length j) (flipValue_lt hj) T hT
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    rw [occurrences_eq_complement hj]
    exact hbound N hN

end GoldenNormality.BinaryComplement
