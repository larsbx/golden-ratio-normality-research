"""Semantic counterexamples and rejection controls for the normality criteria."""

COUNTEREXAMPLES = """import GoldenNormality
namespace GoldenNormality.CriteriaCounterexamples

theorem decoderLeadingZero : wordOfValue 10 2 3 = [0, 3] := by decide

theorem decoderOutOfRange :
    wordOfValue 10 2 100 = [10, 0] ∧
      ¬ InAlphabet 10 (wordOfValue 10 2 100) := by decide

theorem zeroWidthOnlyZero (b j : ℕ) : j < b ^ 0 ↔ j = 0 := by simp

theorem binaryTwo : DigitsAt 2 0 [1, 0] := by
  refine ⟨?_, ?_, True.intro⟩
  · exact digit_of_certificates (b := 2) (n := 0) (q := 0) (r := 1)
      (by decide) (by decide) (by decide)
  · exact digit_of_certificates (b := 2) (n := 1) (q := 1) (r := 2)
      (by decide) (by decide) (by decide)

theorem binaryThree : DigitsAt 2 0 [1, 0, 0] := by
  refine ⟨binaryTwo.1, binaryTwo.2.1, ?_, True.intro⟩
  · exact digit_of_certificates (b := 2) (n := 2) (q := 2) (r := 4)
      (by decide) (by decide) (by decide)

theorem binaryFour : DigitsAt 2 0 [1, 0, 0, 1] := by
  refine ⟨binaryThree.1, binaryThree.2.1, binaryThree.2.2.1, ?_, True.intro⟩
  · exact digit_of_certificates (b := 2) (n := 3) (q := 4) (r := 9)
      (by decide) (by decide) (by decide)

theorem onesTwo : occurrences 2 1 1 2 = 1 :=
  certified_occurrences_sound (b := 2) (value := 1)
    (text := [1, 0]) (pattern := [1])
    (by decide) (by decide) (by decide) binaryTwo (by decide)

theorem onesThree : occurrences 2 1 1 3 = 1 :=
  certified_occurrences_sound (b := 2) (value := 1)
    (text := [1, 0, 0]) (pattern := [1])
    (by decide) (by decide) (by decide) binaryThree (by decide)

theorem onesFour : occurrences 2 1 1 4 = 2 :=
  certified_occurrences_sound (b := 2) (value := 2)
    (text := [1, 0, 0, 1]) (pattern := [1])
    (by decide) (by decide) (by decide) binaryFour (by decide)

theorem discrepancyTwo : Nat.dist (2 ^ 1 * occurrences 2 1 1 2) 2 = 0 := by
  rw [onesTwo]
  decide

theorem discrepancyThree : Nat.dist (2 ^ 1 * occurrences 2 1 1 3) 3 = 1 := by
  rw [onesThree]
  decide

theorem discrepancyFour : Nat.dist (2 ^ 1 * occurrences 2 1 1 4) 4 = 0 := by
  rw [onesFour]
  decide

theorem gapTermNecessary :
    ¬ Nat.dist (2 ^ 1 * occurrences 2 1 1 3) 3 ≤
      max (Nat.dist (2 ^ 1 * occurrences 2 1 1 2) 2)
        (Nat.dist (2 ^ 1 * occurrences 2 1 1 4) 4) := by
  rw [discrepancyTwo, discrepancyThree, discrepancyFour]
  decide

def zeroCheckpoint (_ : ℕ) : ℕ := 0

theorem zeroCheckpoint_budget (b k j T i : ℕ) :
    (max (Nat.dist ((b ^ k) * occurrences b k j (zeroCheckpoint i)) (zeroCheckpoint i))
      (Nat.dist ((b ^ k) * occurrences b k j (zeroCheckpoint (i + 1)))
        (zeroCheckpoint (i + 1))) +
      (zeroCheckpoint (i + 1) - zeroCheckpoint i)) * T ≤ zeroCheckpoint i := by
  simp [zeroCheckpoint]

theorem zeroCheckpoint_not_strictMono : ¬ StrictMono zeroCheckpoint := by
  intro h
  have hbad : (0 : ℕ) < 0 := h (show (0 : ℕ) < 1 by decide)
  exact Nat.lt_irrefl 0 hbad

end GoldenNormality.CriteriaCounterexamples
"""

# Each source is compiled separately and must fail for its specified reason.
REJECTIONS = {
    "out_of_range_decoder_alphabet": ("""import GoldenNormality
open GoldenNormality
example : InAlphabet 10 (wordOfValue 10 2 100) := by decide
""", r"(?i)decide.*proved"),
    "zero_width_roundtrip": ("""import GoldenNormality
open GoldenNormality
example : wordValue 10 (wordOfValue 10 0 1) = 1 := by decide
""", r"(?i)decide.*proved"),
    "omitted_checkpoint_gap": ("""import CriteriaCounterexamples
open GoldenNormality
example :
    Nat.dist (2 ^ 1 * occurrences 2 1 1 3) 3 ≤
      max (Nat.dist (2 ^ 1 * occurrences 2 1 1 2) 2)
        (Nat.dist (2 ^ 1 * occurrences 2 1 1 4) 4) := by
  rw [CriteriaCounterexamples.discrepancyTwo, CriteriaCounterexamples.discrepancyThree,
    CriteriaCounterexamples.discrepancyFour]
  decide
""", r"(?i)decide.*proved"),
    "constant_checkpoint_strict_mono": ("""import CriteriaCounterexamples
open GoldenNormality
example : StrictMono CriteriaCounterexamples.zeroCheckpoint := by
  intro i j hij
  change (0 : ℕ) < 0
  decide
""", r"(?i)decide.*proved"),
    "weakened_interval_quantifier": ("""import Receipts
open GoldenNormality
namespace WeakenedIntervalControl
theorem endpointOnly : Nat.dist (2 ^ 3 * occurrences 2 3 0 222) 222 * 2 ≤ 222 :=
  Receipts.interval_0_0 222 (by decide) (by decide)
example : ∀ N : ℕ, 222 ≤ N → N ≤ 254 →
    Nat.dist (2 ^ 3 * occurrences 2 3 0 N) N * 2 ≤ N :=
  endpointOnly
end WeakenedIntervalControl
""", r"(?i)type mismatch"),
}
