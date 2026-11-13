import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.digit 0 = GoldenNormality.digit 2 0 := by
  rw [firstComplementDigit, firstOriginalDigit]
  decide
