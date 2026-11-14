import SparsityCounterexamples
open GoldenNormality GoldenNormality.SparsityCounterexamples
example : 3 ≤ 2 * occurrences 2 1 1 3 := by
  rw [firstThreeOnes]
  decide
