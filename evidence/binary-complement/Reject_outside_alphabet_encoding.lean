import GoldenNormality
open GoldenNormality
example : ([0, 10] : List ℕ) = [1, 0] := by
  apply wordValue_injective (b := 10) _ (by decide) (by decide) (by decide)
  decide
