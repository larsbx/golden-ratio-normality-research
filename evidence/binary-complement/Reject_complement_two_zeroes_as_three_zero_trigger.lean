import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.convolutionCoefficient 5 →
    BinaryComplement.digit 5 = 0 → BinaryComplement.digit 6 = 0 →
      0 < BinaryComplement.carry 5 := by
  rw [actualTwoZeroTriggerFails.1, actualTwoZeroTriggerFails.2.1,
    actualTwoZeroTriggerFails.2.2.1, actualTwoZeroTriggerFails.2.2.2]
  intro _ _ _
  decide
