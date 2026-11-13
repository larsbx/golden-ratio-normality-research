import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 0 [[true], [true, false], [true, false, false], [true, false, true]]
    [1, 0, 1, 0] := by decide
