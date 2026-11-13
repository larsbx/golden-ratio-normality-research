import SparsityCounterexamples
open GoldenNormality GoldenNormality.BinaryAutomaton GoldenNormality.SparsityCounterexamples
example : 2 * 3 ≤ Blocks.count [1] (powerDigits 7 3) ^ 2 +
    3 * Blocks.count [1] (powerDigits 7 3) + 4 := by
  rw [shiftedZeroThreeCanonical]
  decide
