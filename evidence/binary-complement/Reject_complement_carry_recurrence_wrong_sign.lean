import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 2 * BinaryComplement.carry 2 =
    BinaryComplement.carry 3 - BinaryComplement.signedCoefficient 2 := by
  rw [carryFirstValues.2.2.1, carryFirstValues.2.2.2, firstSignedCoefficients.2.2]
  decide
