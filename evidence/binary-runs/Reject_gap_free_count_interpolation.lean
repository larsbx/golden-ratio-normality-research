import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : Nat.dist (2 * intervalCount 10 (3 * 10)) (3 * 10) * 4 ≤ 3 * 10 := by
  decide
