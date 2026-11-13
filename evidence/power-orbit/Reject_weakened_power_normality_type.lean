import GoldenNormality
open GoldenNormality GoldenNormality.BinaryAutomaton
namespace WeakenedPowerNormality
theorem onlyForward : PowerOrbitNormality → NormalInBase 2 :=
  powerOrbitNormality_iff_normalInBase.mp
example : PowerOrbitNormality ↔ NormalInBase 2 := onlyForward
end WeakenedPowerNormality
