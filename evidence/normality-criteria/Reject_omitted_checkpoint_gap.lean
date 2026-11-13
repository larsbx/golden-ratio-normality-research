import CriteriaCounterexamples
open GoldenNormality
example :
    Nat.dist (2 ^ 1 * occurrences 2 1 1 3) 3 ≤
      max (Nat.dist (2 ^ 1 * occurrences 2 1 1 2) 2)
        (Nat.dist (2 ^ 1 * occurrences 2 1 1 4) 4) := by
  rw [CriteriaCounterexamples.discrepancyTwo, CriteriaCounterexamples.discrepancyThree,
    CriteriaCounterexamples.discrepancyFour]
  decide
