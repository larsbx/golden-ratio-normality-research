import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.occurrences 1 1 3 = GoldenNormality.occurrences 2 1 1 3 := by
  rw [firstThreeComplementCounts.1, firstThreeOriginalCounts.2]
  decide
