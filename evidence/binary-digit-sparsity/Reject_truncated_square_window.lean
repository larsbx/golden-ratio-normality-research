import CheckpointCounterexamples
open GoldenNormality GoldenNormality.BinaryAutomaton GoldenNormality.CheckpointCounterexamples
example : Blocks.count [1, 0, 0] (powerDigits 0 (1 ^ 2)) = 1 := by
  rw [truncatedSquarePrefix]
  decide
