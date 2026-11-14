import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.carry 4 → BinaryComplement.digit 4 = 0 →
    0 < BinaryComplement.carry 5 := by
  rw [laterCarryValues.1, laterCarryValues.2.2, laterCarryValues.2.1]
  intro _ _
  decide
