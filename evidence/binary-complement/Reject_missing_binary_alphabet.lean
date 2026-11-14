import GoldenNormality.BinarySparsity
open GoldenNormality FiniteMathKernels
example : binaryWeight (wordValue 2 [2]) = Blocks.count [1] [2] := by decide
