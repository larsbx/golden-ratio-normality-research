import GoldenNormality.SquareCheckpoints
open GoldenNormality
example (b k j i T : ℕ) (hT : 1 ≤ T) (hi : 12 * T ≤ i)
    (lower : Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint i))
      (squareCheckpoint i) * (4 * T) ≤ squareCheckpoint i)
    (upper : Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint (i + 1)))
      (squareCheckpoint (i + 1)) * (4 * T) ≤ squareCheckpoint (i + 1)) :
    ∀ N : ℕ, squareCheckpoint i ≤ N → N ≤ squareCheckpoint (i + 1) →
      Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N :=
  occurrences_square_interval_bound b k j i (squareCheckpoint i) T hT hi
    (le_refl _) (squareCheckpoint_strictMono.monotone (Nat.le_succ i)) lower upper
