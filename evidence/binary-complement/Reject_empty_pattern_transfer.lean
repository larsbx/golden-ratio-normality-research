import GoldenNormality
open GoldenNormality
example : occurrences 2 0 0 1 = 0 :=
  certified_occurrences_sound (pattern := []) (text := [])
    (by decide) (by decide) (by decide) True.intro (by decide)
