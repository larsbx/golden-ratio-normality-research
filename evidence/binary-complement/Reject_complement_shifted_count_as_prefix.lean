import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : Blocks.count [1] (BinaryComplement.powerDigits 1 2) =
    BinaryComplement.occurrences 1 1 2 := by
  rw [shiftedTwoComplementPower, firstTwoComplementOneCount]
  decide
