import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : StrictMono zeroCheckpoint := by
  intro i j hij
  change (0 : ℕ) < 0
  decide
