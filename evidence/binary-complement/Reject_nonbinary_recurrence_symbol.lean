import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : 2 ∈ powerDigits 0 (0 + 2) := by
  rw [firstTwoCanonical]
  decide
