import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : 1 ∈ powerDigits 1 (1 + 1) := by
  rw [zeroTwoCanonical]
  decide
