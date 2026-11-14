import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.carry 3 → 0 < BinaryComplement.carry 2 := by
  rw [carryFirstValues.2.2.2, carryFirstValues.2.2.1]
  intro _
  decide
