import GoldenNormality.CheckpointBounds

/-!
# Normality from endpoints with vanishing relative gaps

A strictly increasing checkpoint sequence supplies every sufficiently late
starting-position count by interpolation. If the gaps are eventually small
relative to the lower endpoint, convergence at the endpoints is equivalent to
full normality. All estimates use exact natural-number inequalities.

This module proves a criterion. It does not supply the eventual endpoint
estimates for the golden ratio, and no finite collection of checkpoint
certificates supplies those estimates.
-/

namespace GoldenNormality

/-- The relative gaps tend to zero, stated without division: every positive
integer tolerance denominator eventually bounds each gap by that fraction of
the lower checkpoint. Strict increase is a separate hypothesis. -/
def VanishingRelativeGaps (q : ℕ → ℕ) : Prop :=
  ∀ T : ℕ, 1 ≤ T →
    ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i → (q (i + 1) - q i) * T ≤ q i

/-- All-block normality estimates restricted to a specified checkpoint
sequence. The eventual index threshold may depend on the block length, block
value, and tolerance; every index at or above that threshold is required.
No growth condition on the sequence is hidden in this definition. -/
def NormalOnCheckpoints (b : ℕ) (q : ℕ → ℕ) : Prop :=
  2 ≤ b ∧
    ∀ k : ℕ, 1 ≤ k →
      ∀ j : ℕ, j < b ^ k →
        ∀ T : ℕ, 1 ≤ T →
          ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
            Nat.dist ((b ^ k) * occurrences b k j (q i)) (q i) * T ≤ q i

/-- Independent endpoint and gap estimates at tolerance `4*T` imply the
combined interpolation budget at tolerance `T`. The upper endpoint estimate
is scaled by `R`, so the gap estimate also controls this change of scale. -/
theorem checkpoint_budget_of_endpoint_bounds
    (L R lowerError upperError T : ℕ) (hLR : L ≤ R) (hT : 1 ≤ T)
    (lower : lowerError * (4 * T) ≤ L)
    (upper : upperError * (4 * T) ≤ R)
    (gap : (R - L) * (4 * T) ≤ L) :
    (max lowerError upperError + (R - L)) * T ≤ L := by
  have hR : R = L + (R - L) := by omega
  have hgap : R - L ≤ L := by nlinarith
  have hmax : max lowerError upperError * (4 * T) ≤ R := by
    rcases le_total lowerError upperError with h | h
    · rw [max_eq_right h]
      exact upper
    · rw [max_eq_left h]
      exact lower.trans hLR
  nlinarith

/-- Endpoint convergence with an explicit relative-gap budget controls every
intermediate discrepancy. The same base, width, block value, and source
starting-position counts occur throughout. -/
theorem occurrences_interval_bound_of_endpoint_bounds
    (b k j L N R T : ℕ) (hT : 1 ≤ T) (hLN : L ≤ N) (hNR : N ≤ R)
    (lower : Nat.dist ((b ^ k) * occurrences b k j L) L * (4 * T) ≤ L)
    (upper : Nat.dist ((b ^ k) * occurrences b k j R) R * (4 * T) ≤ R)
    (gap : (R - L) * (4 * T) ≤ L) :
    Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N := by
  apply occurrences_interval_bound b k j L N R T hLN hNR
  exact checkpoint_budget_of_endpoint_bounds L R
    (Nat.dist ((b ^ k) * occurrences b k j L) L)
    (Nat.dist ((b ^ k) * occurrences b k j R) R) T
    (hLN.trans hNR) hT lower upper gap

/-- Full normality restricts to every strictly increasing checkpoint sequence.
Only growth to arbitrarily large positions is used in this direction; the
relative-gap condition is not needed. -/
theorem normalOnCheckpoints_of_normalInBase {b : ℕ} {q : ℕ → ℕ}
    (hq : StrictMono q) (normal : NormalInBase b) :
    NormalOnCheckpoints b q := by
  have hqge : ∀ i : ℕ, i ≤ q i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hgrow := hq (Nat.lt_succ_self i)
      exact (Nat.succ_le_succ ih).trans (Nat.succ_le_of_lt hgrow)
  refine ⟨normal.1, ?_⟩
  intro k hk j hj T hT
  obtain ⟨N0, _, hbound⟩ := normal.2 k hk j hj T hT
  refine ⟨N0, ?_⟩
  intro i hi
  exact hbound (q i) (hi.trans (hqge i))

/-- Endpoint estimates on a strictly increasing sequence imply normality when
the relative gaps vanish. Both infinite hypotheses remain explicit. -/
theorem normalInBase_of_normalOnCheckpoints {b : ℕ} {q : ℕ → ℕ}
    (hq : StrictMono q) (hgaps : VanishingRelativeGaps q)
    (normal : NormalOnCheckpoints b q) : NormalInBase b := by
  apply normalInBase_of_checkpoint_bounds normal.1
  intro k hk j hj T hT
  have hfour : 1 ≤ 4 * T := by omega
  obtain ⟨countStart, hcount⟩ := normal.2 k hk j hj (4 * T) hfour
  obtain ⟨gapStart, hgap⟩ := hgaps (4 * T) hfour
  refine ⟨q, hq, max countStart gapStart, ?_⟩
  intro i hi
  have hci : countStart ≤ i := (le_max_left _ _).trans hi
  have hgi : gapStart ≤ i := (le_max_right _ _).trans hi
  exact checkpoint_budget_of_endpoint_bounds (q i) (q (i + 1))
    (Nat.dist ((b ^ k) * occurrences b k j (q i)) (q i))
    (Nat.dist ((b ^ k) * occurrences b k j (q (i + 1))) (q (i + 1))) T
    (hq.monotone (by omega)) hT (hcount i hci)
    (hcount (i + 1) (by omega)) (hgap i hgi)

/-- A fixed strictly increasing sequence with vanishing relative gaps gives
an equivalent endpoint-only normality target. The theorem does not establish
either side for the golden ratio. -/
theorem normalInBase_iff_normalOnCheckpoints (b : ℕ) {q : ℕ → ℕ}
    (hq : StrictMono q) (hgaps : VanishingRelativeGaps q) :
    NormalInBase b ↔ NormalOnCheckpoints b q := by
  exact ⟨normalOnCheckpoints_of_normalInBase hq,
    normalInBase_of_normalOnCheckpoints hq hgaps⟩

end GoldenNormality
