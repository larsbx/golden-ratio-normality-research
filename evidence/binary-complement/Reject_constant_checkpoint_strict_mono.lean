import CriteriaCounterexamples
open GoldenNormality
example : StrictMono CriteriaCounterexamples.zeroCheckpoint := by
  intro i j hij
  change (0 : ℕ) < 0
  decide
