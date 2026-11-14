import GoldenNormality
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
