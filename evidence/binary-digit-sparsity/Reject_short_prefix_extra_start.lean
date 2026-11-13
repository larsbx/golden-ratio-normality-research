import BridgeCounterexamples
open GoldenNormality
example : occurrences 2 3 4 1 = 0 :=
  certified_occurrences_sound (b := 2) (value := 0)
    (pattern := [1, 0, 0]) (text := [1])
    (by decide) (by decide) (by decide)
    BridgeCounterexamples.firstBinaryDigit (by decide)
