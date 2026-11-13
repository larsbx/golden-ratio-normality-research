import GoldenNormality.SparseCheckpoints
import GoldenNormality.PowerOrbit

/-!
# Square checkpoints for the normality target

The checkpoints `i^2` increase strictly and have the exact gap `2*i+1`.
For each positive tolerance denominator `T`, every `i >= 3*T` makes that
gap at most `i^2/T`. Therefore eventual convergence at square checkpoints
is equivalent to the existing full normality target.

The binary specialization expresses the endpoint counts on the computable
power-orbit output words. Its prefix length is `i^2 + pattern.length - 1`,
which supplies exactly `i^2` complete starting positions. Every pattern,
tolerance, eventual index threshold, and subsequent checkpoint remains.
No endpoint frequency estimate for the golden ratio is proved here.
-/

namespace GoldenNormality

/-- Square checkpoints, including the zero checkpoint at index zero. -/
def squareCheckpoint (i : ℕ) : ℕ := i ^ 2

/-- Squares of natural indices form a strictly increasing unbounded sequence. -/
theorem squareCheckpoint_strictMono : StrictMono squareCheckpoint := by
  intro i j hij
  unfold squareCheckpoint
  nlinarith

/-- The exact number of additional starting positions between consecutive squares. -/
theorem squareCheckpoint_gap (i : ℕ) :
    squareCheckpoint (i + 1) - squareCheckpoint i = 2 * i + 1 := by
  unfold squareCheckpoint
  have h : (i + 1) ^ 2 = i ^ 2 + (2 * i + 1) := by ring
  rw [h, Nat.add_sub_cancel_left]

/-- An explicit threshold for each relative gap tolerance. -/
theorem squareCheckpoint_gap_bound {i T : ℕ} (hT : 1 ≤ T) (hi : 3 * T ≤ i) :
    (squareCheckpoint (i + 1) - squareCheckpoint i) * T ≤ squareCheckpoint i := by
  rw [squareCheckpoint_gap]
  unfold squareCheckpoint
  have hipos : 1 ≤ i := by omega
  have hlarge := Nat.mul_le_mul_right i hi
  have hsmall := Nat.mul_le_mul_left T hipos
  nlinarith

/-- Square checkpoint gaps are eventually small relative to the lower endpoint. -/
theorem squareCheckpoint_vanishingRelativeGaps :
    VanishingRelativeGaps squareCheckpoint := by
  intro T hT
  exact ⟨3 * T, fun _ hi => squareCheckpoint_gap_bound hT hi⟩

/-- All-block eventual convergence at squares is exactly the full normality target. -/
theorem normalInBase_iff_squareCheckpoints (b : ℕ) :
    NormalInBase b ↔ NormalOnCheckpoints b squareCheckpoint :=
  normalInBase_iff_normalOnCheckpoints b squareCheckpoint_strictMono
    squareCheckpoint_vanishingRelativeGaps

/-- Endpoint bounds at tolerance `4*T` cover every intermediate start count
once the explicit square-gap threshold `i >= 12*T` holds. -/
theorem occurrences_square_interval_bound (b k j i N T : ℕ)
    (hT : 1 ≤ T) (hi : 12 * T ≤ i)
    (hLN : squareCheckpoint i ≤ N) (hNR : N ≤ squareCheckpoint (i + 1))
    (lower : Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint i))
      (squareCheckpoint i) * (4 * T) ≤ squareCheckpoint i)
    (upper : Nat.dist ((b ^ k) * occurrences b k j (squareCheckpoint (i + 1)))
      (squareCheckpoint (i + 1)) * (4 * T) ≤ squareCheckpoint (i + 1)) :
    Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N := by
  exact occurrences_interval_bound_of_endpoint_bounds b k j
    (squareCheckpoint i) N (squareCheckpoint (i + 1)) T hT hLN hNR lower upper
      (squareCheckpoint_gap_bound (by omega) (by omega))

namespace BinaryAutomaton

/-- The complete open normality target sampled at square numbers of starts.
The positive eventual index threshold may depend on the word and tolerance.
It supplies no estimate at any particular checkpoint by itself.
-/
def PowerOrbitSquareNormality : Prop :=
  ∀ pattern : List ℕ, pattern ≠ [] → InAlphabet 2 pattern →
    ∀ toleranceDenominator : ℕ, 1 ≤ toleranceDenominator →
      ∃ i0 : ℕ, 1 ≤ i0 ∧
        ∀ i : ℕ, i0 ≤ i →
          Nat.dist ((2 ^ pattern.length) *
            Blocks.count pattern (powerDigits 0 (i ^ 2 + pattern.length - 1))) (i ^ 2) *
              toleranceDenominator ≤ i ^ 2

/-- The square-sampled computable word target retains precisely the full binary
normality obligation. The proof combines exact count semantics with the proved
square checkpoint geometry; it assumes no frequency estimate for the orbit.
-/
theorem powerOrbitSquareNormality_iff_normalInBase :
    PowerOrbitSquareNormality ↔ NormalInBase 2 := by
  constructor
  · intro h
    apply (normalInBase_iff_squareCheckpoints 2).mpr
    refine ⟨by decide, ?_⟩
    intro k hk j hj T hT
    obtain ⟨pattern, ha, hlen, hvalue⟩ := exists_word_of_lt (by decide) hj
    have hpat : pattern ≠ [] := List.length_pos_iff.mp (by omega)
    obtain ⟨i0, _, hbound⟩ := h pattern hpat ha T hT
    refine ⟨i0, ?_⟩
    intro i hi
    have hword := hbound i hi
    rw [count_powerDigits hpat ha (i ^ 2), hlen, hvalue] at hword
    simpa only [squareCheckpoint] using hword
  · intro h
    have hs := (normalInBase_iff_squareCheckpoints 2).mp h
    intro pattern hpat ha T hT
    have hk : 1 ≤ pattern.length := List.length_pos_iff.mpr hpat
    obtain ⟨i0, hbound⟩ :=
      hs.2 pattern.length hk (wordValue 2 pattern) (wordValue_lt ha) T hT
    refine ⟨max 1 i0, le_max_left _ _, ?_⟩
    intro i hi
    rw [count_powerDigits hpat ha (i ^ 2)]
    simpa only [squareCheckpoint] using hbound i ((le_max_right _ _).trans hi)

end BinaryAutomaton
end GoldenNormality
