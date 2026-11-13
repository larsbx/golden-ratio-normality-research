import GoldenNormality.SquareCheckpoints
open GoldenNormality GoldenNormality.BinaryAutomaton
namespace WeakenedPowerSquare
theorem oneDirection : PowerOrbitSquareNormality → NormalInBase 2 :=
  powerOrbitSquareNormality_iff_normalInBase.mp
example : PowerOrbitSquareNormality ↔ NormalInBase 2 := oneDirection
end WeakenedPowerSquare
