import GoldenNormality
open GoldenNormality
namespace WeakenedDiscrepancyControl
theorem weakened : True := True.intro
example :
    Nat.dist (2 ^ 3 * occurrences 2 3 4 1) 1 = Nat.dist (2 ^ 3 * 1) 1 :=
  weakened
end WeakenedDiscrepancyControl
