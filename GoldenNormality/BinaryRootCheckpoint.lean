import GoldenNormality.BinaryPartitionCarry
import Mathlib.Data.Nat.Sqrt

/-! Integer square roots give a reusable rational envelope for block checkpoints. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

def rootCap (scale i : ℕ) : ℕ :=
  if i = 0 then 0 else Nat.sqrt (scale ^ 2 * i) + 1

private theorem rootCap_mono (scale : ℕ) : Monotone (rootCap scale) := by
  intro i j hij
  by_cases hi : i = 0
  · simp [rootCap, hi]
  · have hj : j ≠ 0 := by omega
    simpa [rootCap, hi, hj] using
      Nat.succ_le_succ (Nat.sqrt_le_sqrt (Nat.mul_le_mul_left (scale ^ 2) hij))

private theorem sqrt_le_rootCap {scale : ℕ} (hs : 0 < scale) (i : ℕ) :
    Real.sqrt (i : ℝ) ≤ (rootCap scale i : ℝ) / scale := by
  by_cases hi : i = 0
  · simp [hi, rootCap]
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hb : scale ^ 2 * i ≤ (rootCap scale i) ^ 2 := by
    unfold rootCap
    rw [ite_eq_right hi]
    exact (Nat.lt_succ_sqrt' _).le
  have hbR : (scale : ℝ) ^ 2 * i ≤ (rootCap scale i : ℝ) ^ 2 := by exact_mod_cast hb
  apply Real.sqrt_le_iff.mpr
  refine ⟨div_nonneg (Nat.cast_nonneg _) hsR.le, ?_⟩
  rw [div_pow, le_div_iff₀ (pow_pos hsR 2)]
  simpa only [mul_comm] using hbR

/-- Exact integer numerator for the rational upper envelope's pair budget. -/
def rootCheckpointBudget (scale blocks : ℕ) : ℕ :=
  ∑ i ∈ Finset.range blocks,
    (rootCap scale (i + 1) - rootCap scale i) * rootCap scale (blocks - i)

/-- A certificate for an entire checkpoint window, computed from integer square roots. -/
theorem original_zero_count_root_window (scale blocks n : ℕ) (hs : 0 < scale)
    (hN : 2 ≤ blocks * n) (c : ℝ) (hc : 0 ≤ c)
    (hbudget : 2 * c ^ 2 * (rootCheckpointBudget scale blocks : ℝ) /
          (scale : ℝ) ^ 2 * n +
        6 * c * ((rootCap scale blocks : ℝ) / scale) * Real.sqrt n ≤
      (blocks : ℝ) * n) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ blocks ∧
      c * Real.sqrt ((i * n : ℕ) : ℝ) < (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  by_contra! h
  let k := Real.sqrt (n : ℝ)
  let g := fun i : ℕ => c * k * ((rootCap scale i : ℝ) / scale)
  have hk : 0 ≤ k := Real.sqrt_nonneg _
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  have hg₀ : g 0 = 0 := by simp [g, rootCap]
  have hgmono : Monotone g := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hc hk)
    apply div_le_div_of_nonneg_right _ hsR.le
    exact_mod_cast rootCap_mono scale hij
  have hcap : ∀ i ≤ blocks, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤ g i := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simp [hg₀, GoldenNormality.occurrences_zero]
    have hu := h i (by omega) hi
    push_cast at hu
    rw [Real.sqrt_mul (Nat.cast_nonneg i)] at hu
    exact hu.trans (by
      dsimp [g, k]
      calc
        c * (Real.sqrt (i : ℝ) * Real.sqrt (n : ℝ)) =
          c * Real.sqrt (n : ℝ) * Real.sqrt (i : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (sqrt_le_rootCap hs i) (mul_nonneg hc hk))
  have hb := original_zero_count_partition_envelope blocks n hN g hg₀ hgmono hcap
  have hsum : (∑ i ∈ Finset.range blocks, (g (i + 1) - g i) * g (blocks - i)) =
      (c * k / scale) ^ 2 * (rootCheckpointBudget scale blocks : ℝ) := by
    unfold rootCheckpointBudget
    push_cast only [Nat.cast_sum, Nat.cast_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (rootCap_mono scale (Nat.le_succ i))]
    dsimp [g]
    ring
  have hk2 : k ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  rw [hsum] at hb
  dsimp [g] at hb
  have hscale : (c * k / (scale : ℝ)) ^ 2 =
      c ^ 2 / (scale : ℝ) ^ 2 * n := by
    rw [div_pow, mul_pow, hk2]
    ring
  rw [hscale] at hb
  change 2 * c ^ 2 * (rootCheckpointBudget scale blocks : ℝ) /
      (scale : ℝ) ^ 2 * n + 6 * c * ((rootCap scale blocks : ℝ) / scale) * k ≤
      (blocks : ℝ) * n at hbudget
  have hsame : 2 * (c ^ 2 / (scale : ℝ) ^ 2 * (n : ℝ) *
        (rootCheckpointBudget scale blocks : ℝ)) +
      6 * (c * k * ((rootCap scale blocks : ℝ) / scale)) =
      2 * c ^ 2 * (rootCheckpointBudget scale blocks : ℝ) /
        (scale : ℝ) ^ 2 * n + 6 * c * ((rootCap scale blocks : ℝ) / scale) * k := by ring
  linarith only [hb, hbudget, hsame]

private def rootCap64Values : List ℕ :=
  [0, 10001, 14143, 17321, 20001, 22361, 24495, 26458, 28285, 30001, 31623, 33167, 34642, 36056, 37417, 38730, 40001, 41232, 42427, 43589, 44722, 45826, 46905, 47959, 48990, 50001, 50991, 51962, 52916, 53852, 54773, 55678, 56569, 57446, 58310, 59161, 60001, 60828, 61645, 62450, 63246, 64032, 64808, 65575, 66333, 67083, 67824, 68557, 69283, 70001, 70711, 71415, 72112, 72802, 73485, 74162, 74834, 75499, 76158, 76812, 77460, 78103, 78741, 79373, 80001]

private theorem rootCap_10000_at (i : ℕ) (hi : i ≤ 64) :
    rootCap 10000 i = rootCap64Values[i]! := by
  by_cases hz : i = 0
  · subst i
    simp [rootCap, rootCap64Values]
  unfold rootCap
  rw [ite_eq_right hz]
  have hcheck (j : ℕ) (hj₀ : 0 < j) (hj : j ≤ 64) :
      (rootCap64Values[j]! - 1) ^ 2 ≤ 10000 ^ 2 * j ∧
        10000 ^ 2 * j < ((rootCap64Values[j]! - 1) + 1) ^ 2 := by
    interval_cases j <;> decide
  have hpos : 0 < rootCap64Values[i]! := by
    interval_cases i <;> first | contradiction | decide
  have he := Nat.eq_sqrt'.mpr (hcheck i (Nat.pos_of_ne_zero hz) hi)
  rw [← he, Nat.sub_add_cancel (show 1 ≤ _ from hpos)]

/-- For every width at least 65536, one of 64 checkpoints exceeds the 0.794 envelope. -/
theorem original_zero_count_sixty_four_window (n : ℕ) (hn : 65536 ≤ n) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 64 ∧
      (397 / 500 : ℝ) * Real.sqrt ((i * n : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  apply original_zero_count_root_window 10000 64 n (by decide) (by omega) _ (by norm_num)
  have hbudget : rootCheckpointBudget 10000 64 = 5063329433 := by
    unfold rootCheckpointBudget
    trans ∑ i ∈ Finset.range 64,
      (rootCap64Values[i + 1]! - rootCap64Values[i]!) * rootCap64Values[64 - i]!
    · apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [rootCap_10000_at (i + 1) (by omega), rootCap_10000_at i (by omega),
        rootCap_10000_at (64 - i) (by omega)]
    · decide
  have hcap : rootCap 10000 64 = 80001 := by
    rw [rootCap_10000_at 64 (by decide)]
    decide
  rw [hbudget, hcap]
  push_cast
  let k := Real.sqrt (n : ℝ)
  have hk : (256 : ℝ) ≤ k := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k from Real.sqrt_nonneg _)
  have hk2 : (n : ℝ) = k ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  have hk_eq : Real.sqrt (n : ℝ) = k := rfl
  rw [hk_eq, hk2]
  change 2 * (397 / 500 : ℝ) ^ 2 * 5063329433 / 10000 ^ 2 * k ^ 2 +
    6 * (397 / 500 : ℝ) * (80001 / 10000) * k ≤ 64 * k ^ 2
  nlinarith only [hprod, hk]

end GoldenNormality.BinaryComplement
