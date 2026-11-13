import GoldenNormality
open GoldenNormality
example : ([0, 1] : List ℕ) = [1] := by
  apply wordValue_injective (b := 10) (by decide) (by decide) _ (by decide)
  decide
