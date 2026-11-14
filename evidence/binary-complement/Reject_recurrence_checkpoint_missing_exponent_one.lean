import GoldenNormality.BinaryRecurrence
open GoldenNormality
example : 1 ≤ occurrences 2 1 0 (2 ^ 1 - 2) := by
  change 1 ≤ occurrences 2 1 0 0
  rw [occurrences_zero]
  decide
