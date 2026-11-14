import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : (powerDigits 1 2).length ≤ 1 := by
  rw [zeroTwoCanonical]
  decide
