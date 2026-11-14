import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.actualDigits 1 2 = BinaryComplement.actualDigits 0 2 := by
  rw [shiftedTwoComplement, firstTwoComplement]
  decide
