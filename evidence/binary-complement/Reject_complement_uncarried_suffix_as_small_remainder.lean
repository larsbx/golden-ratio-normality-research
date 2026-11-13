import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.convolutionSuffix 4 < (2 : ℤ) ^ 4 := by
  rw [uncarriedSuffixExceedsScale]
  decide
