import GoldenNormality.SquareCheckpoints
open GoldenNormality
namespace WeakenedSquareEventual
theorem oneIndex (b k j T : ℕ) :
    Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint 0))
      (squareCheckpoint 0) * T ≤ squareCheckpoint 0 := by
  simp [squareCheckpoint]
example (b k j T : ℕ) : ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
    Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint i))
      (squareCheckpoint i) * T ≤ squareCheckpoint i := oneIndex b k j T
end WeakenedSquareEventual
