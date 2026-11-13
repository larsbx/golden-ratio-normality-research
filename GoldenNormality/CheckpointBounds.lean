import GoldenNormality.FrequencyBridge
import GoldenNormality.Normality
import Mathlib.Data.Nat.Find

/-!
# Exact bounds between certified checkpoints

Occurrence counts are monotone in the number of starting positions.  This
alone bounds every intermediate discrepancy by the larger endpoint
discrepancy plus the distance between the endpoints.  The finite result can
consume two independently source-bound prefix counts for the same pattern.

The final criterion retains an infinite hypothesis: for every block and
positive tolerance denominator, a strictly increasing sequence of checkpoints
must satisfy the endpoint budget at every sufficiently late interval.  No
such eventual budget for the golden ratio is established here.
-/

namespace GoldenNormality

/-- Extending the observed prefix of starting positions cannot remove a match. -/
theorem occurrences_monotone (b k j : ℕ) : Monotone (occurrences b k j) := by
  apply monotone_nat_of_le_succ
  intro N
  unfold occurrences
  rw [List.range_succ, List.countP_append]
  omega

/-- A monotone count gives both sides of an intermediate discrepancy bound.
This uses no estimate on the number of new matches inside the interval. -/
theorem occurrences_discrepancy_interpolation (b k j L N R : ℕ)
    (hLN : L ≤ N) (hNR : N ≤ R) :
    Nat.dist ((b ^ k) * occurrences b k j N) N ≤
      max (Nat.dist ((b ^ k) * occurrences b k j L) L)
        (Nat.dist ((b ^ k) * occurrences b k j R) R) + (R - L) := by
  have hleft := Nat.mul_le_mul_left (b ^ k) (occurrences_monotone b k j hLN)
  have hright := Nat.mul_le_mul_left (b ^ k) (occurrences_monotone b k j hNR)
  have hlow := Nat.dist_tri_right ((b ^ k) * occurrences b k j L) L
  have hupp := Nat.dist_tri_right' ((b ^ k) * occurrences b k j R) R
  have hmaxL := le_max_left
    (Nat.dist ((b ^ k) * occurrences b k j L) L)
    (Nat.dist ((b ^ k) * occurrences b k j R) R)
  have hmaxR := le_max_right
    (Nat.dist ((b ^ k) * occurrences b k j L) L)
    (Nat.dist ((b ^ k) * occurrences b k j R) R)
  unfold Nat.dist at *
  omega

/-- A single endpoint budget proves the normality-shaped finite inequality at
every number of starts in the closed interval. -/
theorem occurrences_interval_bound (b k j L N R T : ℕ)
    (hLN : L ≤ N) (hNR : N ≤ R)
    (budget :
      (max (Nat.dist ((b ^ k) * occurrences b k j L) L)
        (Nat.dist ((b ^ k) * occurrences b k j R) R) + (R - L)) * T ≤ L) :
    Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N := by
  exact (Nat.mul_le_mul_right T
    (occurrences_discrepancy_interpolation b k j L N R hLN hNR)).trans
      (budget.trans hLN)

/-- Two certified words transfer an endpoint budget to every intermediate
number of starts.  Both words must bind to the same actual prefix, base, and
nonempty alphabet pattern; their lengths retain the complete-window formula.
-/
theorem certified_interval_bound {b lowerCount upperCount N T : ℕ} (hb : 2 ≤ b)
    {lowerText upperText pattern : List ℕ}
    (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (lowerDigits : DigitsAt b 0 lowerText) (upperDigits : DigitsAt b 0 upperText)
    (lowerExact : Blocks.count pattern lowerText = lowerCount)
    (upperExact : Blocks.count pattern upperText = upperCount)
    (hLN : lowerText.length + 1 - pattern.length ≤ N)
    (hNR : N ≤ upperText.length + 1 - pattern.length)
    (budget :
      (max (Nat.dist ((b ^ pattern.length) * lowerCount)
          (lowerText.length + 1 - pattern.length))
        (Nat.dist ((b ^ pattern.length) * upperCount)
          (upperText.length + 1 - pattern.length)) +
        ((upperText.length + 1 - pattern.length) -
          (lowerText.length + 1 - pattern.length))) * T ≤
        lowerText.length + 1 - pattern.length) :
    Nat.dist ((b ^ pattern.length) *
      occurrences b pattern.length (wordValue b pattern) N) N * T ≤ N := by
  apply occurrences_interval_bound b pattern.length (wordValue b pattern)
    (lowerText.length + 1 - pattern.length) N
    (upperText.length + 1 - pattern.length) T hLN hNR
  rw [certified_occurrences_sound hb hpat ha lowerDigits lowerExact,
    certified_occurrences_sound hb hpat ha upperDigits upperExact]
  exact budget

/-- Consecutive intervals of a strictly increasing natural sequence cover
every number at or above any chosen checkpoint. -/
theorem checkpoint_interval_covers {q : ℕ → ℕ} (hq : StrictMono q)
    (i0 N : ℕ) (hstart : q i0 ≤ N) :
    ∃ i : ℕ, i0 ≤ i ∧ q i ≤ N ∧ N ≤ q (i + 1) := by
  have hqge : ∀ i : ℕ, i ≤ q i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hgrow := hq (Nat.lt_succ_self i)
      exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hgrow)
  have hex : ∃ i : ℕ, N < q i :=
    ⟨N + 1, lt_of_lt_of_le (Nat.lt_succ_self N) (hqge (N + 1))⟩
  let first := Nat.find hex
  have hfirst : N < q first := Nat.find_spec hex
  have hi0 : i0 < first := by
    by_contra h
    have hle : first ≤ i0 := by omega
    have hqle := hq.monotone hle
    omega
  refine ⟨first - 1, by omega, ?_, ?_⟩
  · have hless : first - 1 < first := by omega
    have hminimal := Nat.find_min hex hless
    omega
  · have he : first - 1 + 1 = first := by omega
    rw [he]
    omega

/-- Conditional checkpoint criterion.  Every valid block and every positive
tolerance denominator must have a strictly increasing, infinite checkpoint
sequence whose endpoint budget holds at every sufficiently late interval.
The sequence and threshold may depend on the block and tolerance.

This theorem proves the implication only; it supplies no eventual budget for
the actual golden-ratio occurrence counts.
-/
theorem normalInBase_of_checkpoint_bounds {b : ℕ} (hb : 2 ≤ b)
    (checkpoints : ∀ k : ℕ, 1 ≤ k →
      ∀ j : ℕ, j < b ^ k →
        ∀ T : ℕ, 1 ≤ T →
          ∃ q : ℕ → ℕ, StrictMono q ∧
            ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
              (max (Nat.dist ((b ^ k) * occurrences b k j (q i)) (q i))
                (Nat.dist ((b ^ k) * occurrences b k j (q (i + 1))) (q (i + 1))) +
                (q (i + 1) - q i)) * T ≤ q i) :
    NormalInBase b := by
  refine ⟨hb, ?_⟩
  intro k hk j hj T hT
  obtain ⟨q, hq, i0, hbudget⟩ := checkpoints k hk j hj T hT
  refine ⟨max 1 (q i0), le_max_left _ _, ?_⟩
  intro N hN
  have hstart : q i0 ≤ N := (le_max_right _ _).trans hN
  obtain ⟨i, hi, hLN, hNR⟩ := checkpoint_interval_covers hq i0 N hstart
  exact occurrences_interval_bound b k j (q i) N (q (i + 1)) T
    hLN hNR (hbudget i hi)

end GoldenNormality
