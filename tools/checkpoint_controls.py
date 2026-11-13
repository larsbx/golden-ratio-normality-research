"""Semantic controls for checkpoint geometry, eventual types, and complete starts.

The finite count model below is deliberately separate from the golden ratio.
Its arbitrary-scale interval refutes gap-free single-count interpolation; it
does not refute an all-block normality criterion at geometric checkpoints.
"""

COUNTEREXAMPLES = """import GoldenNormality.SquareCheckpoints
namespace GoldenNormality.CheckpointCounterexamples
open BinaryAutomaton

def zeroCheckpoint (_ : ℕ) : ℕ := 0

theorem zeroCheckpointGaps : VanishingRelativeGaps zeroCheckpoint := by
  intro T _
  exact ⟨0, by intros; simp [zeroCheckpoint]⟩

theorem zeroCheckpointNormal (b : ℕ) (hb : 2 ≤ b) :
    NormalOnCheckpoints b zeroCheckpoint := by
  refine ⟨hb, ?_⟩
  intro k _ j _ T _
  exact ⟨0, by intros; simp [zeroCheckpoint]⟩

theorem zeroCheckpointNotStrict : ¬ StrictMono zeroCheckpoint := by
  intro h
  have hbad : (0 : ℕ) < 0 := h (show (0 : ℕ) < 1 by decide)
  exact Nat.lt_irrefl 0 hbad

def geometricCheckpoint (i : ℕ) : ℕ := 2 ^ i

theorem geometricGap (i : ℕ) :
    geometricCheckpoint (i + 1) - geometricCheckpoint i = geometricCheckpoint i := by
  unfold geometricCheckpoint
  rw [pow_succ]
  omega

theorem geometricGapsDoNotVanish : ¬ VanishingRelativeGaps geometricCheckpoint := by
  intro h
  obtain ⟨i0, hbound⟩ := h 2 (by decide)
  have hbad := hbound i0 (le_refl _)
  rw [geometricGap] at hbad
  have hpositive : 0 < geometricCheckpoint i0 := pow_pos (by decide) _
  omega

theorem squareStartsAtZero : squareCheckpoint 0 = 0 := by decide

theorem squareGapThreshold :
    (squareCheckpoint (3 + 1) - squareCheckpoint 3) * 1 ≤ squareCheckpoint 3 :=
  squareCheckpoint_gap_bound (by decide) (by decide)

theorem squareGapTooEarly :
    ¬ (squareCheckpoint (2 + 1) - squareCheckpoint 2) * 1 ≤ squareCheckpoint 2 := by
  decide

-- An abstract finite count model, with each successive increment in {0,1}.
-- It is not an occurrence count of the golden ratio and makes no all-block claim.
def intervalCount (M N : ℕ) : ℕ := min N (2 * M) / 2 + min (N - 2 * M) M

theorem intervalCount_zero (M : ℕ) : intervalCount M 0 = 0 := by
  simp [intervalCount]

theorem intervalCount_step (M N : ℕ) :
    intervalCount M N ≤ intervalCount M (N + 1) ∧
      intervalCount M (N + 1) ≤ intervalCount M N + 1 := by
  unfold intervalCount
  omega

theorem intervalCount_monotone (M : ℕ) : Monotone (intervalCount M) := by
  apply monotone_nat_of_le_succ
  intro N
  exact (intervalCount_step M N).1

theorem intervalCount_bounded (M N : ℕ) : intervalCount M N ≤ N := by
  unfold intervalCount
  omega

theorem intervalCount_lower (M : ℕ) : intervalCount M (2 * M) = M := by
  unfold intervalCount
  omega

theorem intervalCount_middle (M : ℕ) : intervalCount M (3 * M) = 2 * M := by
  unfold intervalCount
  omega

theorem intervalCount_upper (M : ℕ) : intervalCount M (4 * M) = 2 * M := by
  unfold intervalCount
  omega

theorem intervalEndpointsBalanced (M : ℕ) :
    Nat.dist (2 * intervalCount M (2 * M)) (2 * M) = 0 ∧
      Nat.dist (2 * intervalCount M (4 * M)) (4 * M) = 0 := by
  rw [intervalCount_lower, intervalCount_upper]
  constructor
  · simp
  · have heq : 2 * (2 * M) = 4 * M := by omega
    rw [heq]
    simp

theorem intervalMiddleDiscrepancy (M : ℕ) :
    Nat.dist (2 * intervalCount M (3 * M)) (3 * M) = M := by
  rw [intervalCount_middle]
  unfold Nat.dist
  omega

theorem intervalMiddleFails (M : ℕ) (hM : 1 ≤ M) :
    ¬ Nat.dist (2 * intervalCount M (3 * M)) (3 * M) * 4 ≤ 3 * M := by
  rw [intervalMiddleDiscrepancy]
  omega

theorem firstThreeBinding :
    PowerOrbitAt 0 [[true], [true, false], [true, false, true]] [1, 0, 0] := by
  decide

theorem firstOneBinding : PowerOrbitAt 0 [[true]] [1] := by decide

theorem firstThreeCanonical : powerDigits 0 3 = [1, 0, 0] :=
  (powerOrbitAt_eq_powerDigits firstThreeBinding).symm

theorem firstOneCanonical : powerDigits 0 1 = [1] :=
  (powerOrbitAt_eq_powerDigits firstOneBinding).symm

theorem oneSquareWidthThreeCount :
    Blocks.count [1, 0, 0] (powerDigits 0 (1 ^ 2 + [1, 0, 0].length - 1)) = 1 := by
  change Blocks.count [1, 0, 0] (powerDigits 0 3) = 1
  rw [firstThreeCanonical]
  decide

theorem truncatedSquarePrefix :
    Blocks.count [1, 0, 0] (powerDigits 0 (1 ^ 2)) = 0 := by
  change Blocks.count [1, 0, 0] (powerDigits 0 1) = 0
  rw [firstOneCanonical]
  decide

end GoldenNormality.CheckpointCounterexamples
"""

REJECTIONS = {
    "premature_square_gap": ("""import GoldenNormality.SquareCheckpoints
open GoldenNormality
example : (squareCheckpoint (2 + 1) - squareCheckpoint 2) * 1 ≤ squareCheckpoint 2 := by
  decide
""", r"(?i)decide.*proved"),
    "geometric_relative_gap": ("""import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : (geometricCheckpoint (4 + 1) - geometricCheckpoint 4) * 2 ≤
    geometricCheckpoint 4 := by decide
""", r"(?i)decide.*proved"),
    "zero_checkpoint_growth": ("""import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : StrictMono zeroCheckpoint := by
  intro i j hij
  change (0 : ℕ) < 0
  decide
""", r"(?i)decide.*proved"),
    "gap_free_count_interpolation": ("""import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : Nat.dist (2 * intervalCount 10 (3 * 10)) (3 * 10) * 4 ≤ 3 * 10 := by
  decide
""", r"(?i)decide.*proved"),
    "truncated_square_window": ("""import CheckpointCounterexamples
open GoldenNormality GoldenNormality.BinaryAutomaton GoldenNormality.CheckpointCounterexamples
example : Blocks.count [1, 0, 0] (powerDigits 0 (1 ^ 2)) = 1 := by
  rw [truncatedSquarePrefix]
  decide
""", r"(?i)decide.*proved"),
    "weakened_square_interval_type": ("""import GoldenNormality.SquareCheckpoints
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
""", r"(?i)type mismatch"),
    "weakened_square_eventual_type": ("""import GoldenNormality.SquareCheckpoints
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
""", r"(?i)type mismatch"),
    "weakened_power_square_iff": ("""import GoldenNormality.SquareCheckpoints
open GoldenNormality GoldenNormality.BinaryAutomaton
namespace WeakenedPowerSquare
theorem oneDirection : PowerOrbitSquareNormality → NormalInBase 2 :=
  powerOrbitSquareNormality_iff_normalInBase.mp
example : PowerOrbitSquareNormality ↔ NormalInBase 2 := oneDirection
end WeakenedPowerSquare
""", r"(?i)type mismatch"),
}
