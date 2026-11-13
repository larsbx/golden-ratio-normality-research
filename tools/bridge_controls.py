"""Semantic counterexamples and rejection controls for the frequency bridge."""

COUNTEREXAMPLES = """import GoldenNormality
namespace GoldenNormality.BridgeCounterexamples

theorem leadingZeroCollision :
    wordValue 10 [0, 1] = wordValue 10 [1] ∧ ([0, 1] : List ℕ) ≠ [1] := by decide

theorem outsideAlphabetCollision :
    wordValue 10 [0, 10] = wordValue 10 [1, 0] ∧
      ([0, 10] : List ℕ).length = [1, 0].length ∧
      ([0, 10] : List ℕ) ≠ [1, 0] ∧ ¬ InAlphabet 10 [0, 10] := by decide

theorem emptyPatternMismatch :
    Blocks.count ([] : List ℕ) [1] = 0 ∧ occurrences 2 0 0 1 = 1 := by
  constructor
  · decide
  · simp [occurrences, blockValue]

theorem firstBinaryDigit : DigitsAt 2 0 [1] := by
  constructor
  · exact digit_of_certificates (b := 2) (n := 0) (q := 0) (r := 1)
      (by decide) (by decide) (by decide)
  · trivial

theorem firstBinaryBlock : DigitsAt 2 0 [1, 0, 0] := by
  refine ⟨firstBinaryDigit.1, ?_, ?_, True.intro⟩
  · exact digit_of_certificates (b := 2) (n := 1) (q := 1) (r := 2)
      (by decide) (by decide) (by decide)
  · exact digit_of_certificates (b := 2) (n := 2) (q := 2) (r := 4)
      (by decide) (by decide) (by decide)

theorem shortPrefixMismatch :
    Blocks.count [1, 0, 0] [1] = 0 ∧ occurrences 2 3 4 1 = 1 := by
  constructor
  · decide
  · exact certified_occurrences_sound (pattern := [1, 0, 0])
      (by decide) (by decide) (by decide) firstBinaryBlock (by decide)

end GoldenNormality.BridgeCounterexamples
"""

# Each rejection is compiled separately: a missing tool, timeout, crash, or
# failure in a different control cannot be mistaken for the intended result.
REJECTIONS = {
    "unequal_length_encoding": ("""import GoldenNormality
open GoldenNormality
example : ([0, 1] : List ℕ) = [1] := by
  apply wordValue_injective (b := 10) (by decide) (by decide) _ (by decide)
  decide
""", r"(?i)decide.*proved"),
    "outside_alphabet_encoding": ("""import GoldenNormality
open GoldenNormality
example : ([0, 10] : List ℕ) = [1, 0] := by
  apply wordValue_injective (b := 10) _ (by decide) (by decide) (by decide)
  decide
""", r"(?i)decide.*proved"),
    "empty_pattern_transfer": ("""import GoldenNormality
open GoldenNormality
example : occurrences 2 0 0 1 = 0 :=
  certified_occurrences_sound (pattern := []) (text := [])
    (by decide) (by decide) (by decide) True.intro (by decide)
""", r"(?i)decide.*proved"),
    "short_prefix_extra_start": ("""import BridgeCounterexamples
open GoldenNormality
example : occurrences 2 3 4 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (pattern := [1, 0, 0]) (text := [1])
    (by decide) (by decide) (by decide)
    BridgeCounterexamples.firstBinaryDigit (by decide)
""", r"(?i)type mismatch"),
    "weakened_discrepancy_type": ("""import GoldenNormality
open GoldenNormality
namespace WeakenedDiscrepancyControl
theorem weakened : True := True.intro
example :
    Nat.dist (2 ^ 3 * occurrences 2 3 4 1) 1 = Nat.dist (2 ^ 3 * 1) 1 :=
  weakened
end WeakenedDiscrepancyControl
""", r"(?i)type mismatch"),
}
