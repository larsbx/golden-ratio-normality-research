import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.scaledFloor 0 = (2 : ℤ) ^ 0 - GoldenNormality.scaledFloor 2 0 := by
  rw [betaFloor0, originalFloor0]
  decide
