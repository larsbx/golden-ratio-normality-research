import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.carry 0 = BinaryComplement.prefixResidual 0 % (2 : ℤ) ^ 0 := by
  rw [carryFirstValues.1]
  norm_num only [BinaryComplement.prefixResidual, BinaryComplement.quadraticResidual,
    betaFloor0, pow_zero]
  decide
