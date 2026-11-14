import GoldenNormality.BinarySemicircleCarry

/-! A positive carry of size one cannot repeat across a zero digit unless
the convolution coefficient comes from a diagonal pair. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

private theorem one_pair_of_coefficient_one (n : ℕ) (hc : convolutionCoefficient n = 1) :
    ∃ i < n, digit i = 1 ∧ digit (n - 1 - i) = 1 := by
  by_contra! h
  have hz : convolutionCoefficient n = 0 := by
    unfold convolutionCoefficient
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have h₁ := digit_range i
    have h₂ := digit_range (n - 1 - i)
    by_cases hzero : digit i = 0
    · simp [hzero]
    · have he : digit i = 1 := by omega
      have he' : digit (n - 1 - i) ≠ 1 := h i hi' he
      rw [he, show digit (n - 1 - i) = 0 by omega, mul_zero]
  omega

/-- A coefficient of one must come from a diagonal pair. -/
theorem convolutionCoefficient_one_diagonal (n : ℕ) (hc : convolutionCoefficient n = 1) :
    n = 2 * (n / 2) + 1 ∧ digit (n / 2) = 1 := by
  obtain ⟨i, hi, hd, hj⟩ := one_pair_of_coefficient_one n hc
  let j := n - 1 - i
  have hji : n - 1 - j = i := by dsimp [j]; omega
  have he : i = j := by
    by_contra hne
    have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_range.mpr hi
      · exact Finset.mem_range.mpr (by dsimp [j]; omega)
    have hpair := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun k => digit k * digit (n - 1 - k)) hsub
      (fun k _ _ => mul_nonneg (digit_range k).1 (digit_range _).1)
    change (∑ k ∈ ({i, j} : Finset ℕ), digit k * digit (n - 1 - k)) ≤
      convolutionCoefficient n at hpair
    rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton, hc, hji, hd, hj] at hpair
    omega
  have hi' : n / 2 = i := by dsimp [j] at he; omega
  exact ⟨by dsimp [j] at he; omega, by rwa [hi']⟩

/-- The size-one carry indicator. -/
noncomputable def unitCarryIndicator (n : ℕ) : ℤ := if carry n = 1 then 1 else 0

private noncomputable def diagonalIndicator (n : ℕ) : ℤ :=
  if n % 2 = 1 then digit (n / 2) else 0

private theorem diagonal_nonneg (n : ℕ) : 0 ≤ diagonalIndicator n := by
  unfold diagonalIndicator
  split
  · exact (digit_range _).1
  · exact le_rfl

private theorem unit_pair_budget (n : ℕ) :
    unitCarryIndicator n + unitCarryIndicator (n + 1) ≤
      positiveCarryIndicator n + digit n + diagonalIndicator n := by
  have hd := digit_range n
  have hdiag := diagonal_nonneg n
  have hp : 0 ≤ positiveCarryIndicator n := le_min (by decide) (le_max_right _ _)
  have hind (hc : 0 < carry n) : positiveCarryIndicator n = 1 := by
    unfold positiveCarryIndicator positiveCarry
    exact min_eq_left ((show 1 ≤ carry n by omega).trans (le_max_left _ _))
  unfold unitCarryIndicator
  by_cases h₁ : carry n = 1
  · rw [ite_eq_left h₁, hind (by omega)]
    by_cases h₂ : carry (n + 1) = 1
    · rw [ite_eq_left h₂]
      by_cases hz : digit n = 0
      · have hr := carry_recurrence n
        unfold signedCoefficient at hr
        have hc : convolutionCoefficient n = 1 := by omega
        obtain ⟨hn, hd'⟩ := convolutionCoefficient_one_diagonal n hc
        have ho : n % 2 = 1 := by omega
        simp [diagonalIndicator, ho, hd', hz]
      · rw [show digit n = 1 by omega]
        omega
    · rw [ite_eq_right h₂]
      omega
  · rw [ite_eq_right h₁]
    by_cases h₂ : carry (n + 1) = 1
    · rw [ite_eq_left h₂]
      by_cases hz : digit n = 0
      · rw [hind (carry_positive_of_zero_step n hz (by omega))]
        omega
      · omega
    · rw [ite_eq_right h₂]
      omega

private theorem diagonal_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, diagonalIndicator i) ≤ ∑ i ∈ Finset.range N, digit i := by
  have hpair (n : ℕ) :
      (∑ i ∈ Finset.range (2 * n), diagonalIndicator i) = ∑ i ∈ Finset.range n, digit i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      simp [diagonalIndicator, show (2 * n + 1) / 2 = n by omega]
  let k := N / 2
  have hcases : N = 2 * k ∨ N = 2 * k + 1 := by dsimp [k]; omega
  have h : (∑ i ∈ Finset.range N, diagonalIndicator i) = ∑ i ∈ Finset.range k, digit i := by
    rcases hcases with hk | hk
    · rw [hk, hpair]
    · rw [hk, Finset.sum_range_succ, hpair]
      simp [diagonalIndicator]
  rw [h]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by dsimp [k]; omega)) (fun i _ _ => (digit_range i).1)

/-- At most half the positive carries can have size one, up to the digit and
diagonal correction. The right endpoint is retained in telescoping. -/
theorem twice_unitCarry_sum_le (N : ℕ) :
    2 * (∑ i ∈ Finset.range N, unitCarryIndicator i) ≤
      (∑ i ∈ Finset.range N, positiveCarryIndicator i) +
        2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  have htel (n : ℕ) :
      2 * (∑ i ∈ Finset.range n, unitCarryIndicator i) + unitCarryIndicator n ≤
        (∑ i ∈ Finset.range n, positiveCarryIndicator i) +
        (∑ i ∈ Finset.range n, digit i) + ∑ i ∈ Finset.range n, diagonalIndicator i := by
    induction n with
    | zero => simp [unitCarryIndicator]
    | succ n ih =>
      simp only [Finset.sum_range_succ] at *
      have h := unit_pair_budget n
      omega
  have hnonneg : 0 ≤ unitCarryIndicator N := by unfold unitCarryIndicator; split <;> omega
  have h := diagonal_sum_le N
  have h' := htel N
  rw [digit_sum_eq_original_zeros] at h h'
  omega

/-- The gap count and the size-one restriction give a stronger lower budget
for truncated convolution mass. -/
theorem original_zero_count_unit_carry_bound (N : ℕ) (hN : 2 ≤ N) :
    3 * (N : ℤ) ≤ 4 * (∑ i ∈ Finset.range N, convolutionCoefficient i) +
      20 * (GoldenNormality.occurrences 2 1 0 N : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have hc := positiveCarry_sum_le 0 N
  have hzero : positiveCarry 0 = 0 := by simp [positiveCarry]
  simp only [Nat.zero_add, hzero, add_zero] at hc
  have hmass := Finset.sum_le_sum (s := Finset.range N) (f := fun i =>
      2 * positiveCarryIndicator i) (g := fun i => positiveCarry i + unitCarryIndicator i)
    (fun i _ => by
      unfold positiveCarryIndicator positiveCarry unitCarryIndicator
      by_cases h : carry i = 1
      · simp [h]
      · rw [ite_eq_right h]
        by_cases h₀ : carry i ≤ 0
        · simp [max_eq_right h₀]
        · have h₂ : 2 ≤ carry i := by omega
          rw [max_eq_left (by omega), min_eq_left (by omega)]
          omega)
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hmass
  have hu := twice_unitCarry_sum_le N
  have hg := prefix_le_positive_count_and_zeros N
  omega

/-- At arbitrarily late prefixes, the normalized zero count exceeds
every nonnegative constant below `√(3/π)`. -/
theorem original_zero_count_exceeds_of_pi_mul_sq_lt_three (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 3) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let δ := 3 - Real.pi * c ^ 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA⟩ := exists_nat_gt ((4 * c ^ 2 + 20 * c) / δ)
  let k := A + 1
  let K := k ^ 2
  let n := M + 2
  have hK : 1 ≤ K := by
    change 1 ≤ (A + 1) ^ 2
    exact Nat.one_le_pow _ _ (by omega)
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hN : 2 ≤ K * n := hn.trans (by simpa using Nat.mul_le_mul_right n hK)
  have hsqrt : Real.sqrt (K : ℝ) = k := by
    dsimp [K]
    push_cast
    exact Real.sqrt_sq (Nat.cast_nonneg _)
  have hnroot : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    exact ⟨by positivity, by nlinarith [mul_nonneg (sub_nonneg.mpr hnR) (Nat.cast_nonneg n)]⟩
  by_contra! h
  have hcap : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
      c * Real.sqrt ((i * n : ℕ) : ℝ) := by
    intro i _
    by_cases hi : i = 0
    · simp [hi, GoldenNormality.occurrences_zero]
    apply h
    have hi' : 1 ≤ i := by omega
    have hmul : n ≤ i * n := by simpa using Nat.mul_le_mul_right n hi'
    exact (show M ≤ n by dsimp [n]; omega).trans hmul
  have hmass := convolution_sum_le_succ_area_envelope K n c hc hcap
  have hb := Int.cast_le (R := ℝ).mpr (original_zero_count_unit_carry_bound (K * n) hN)
  push_cast at hb
  have hend := hcap K le_rfl
  push_cast at hend
  rw [Real.sqrt_mul (Nat.cast_nonneg K), hsqrt] at hend
  have hπ : Real.pi ≤ 4 := Real.pi_le_four
  have herr := mul_le_mul_of_nonneg_right hπ (show 0 ≤ c ^ 2 * (n : ℝ) by positivity)
  have hk : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k by dsimp [k]; omega)
  have herr' := mul_le_mul_of_nonneg_left hk
    (show 0 ≤ 4 * c ^ 2 * (n : ℝ) by positivity)
  have hlin := mul_le_mul_of_nonneg_left hnroot
    (show 0 ≤ 20 * c * (k : ℝ) by positivity)
  have hKcast : (K : ℝ) = (k : ℝ) ^ 2 := by dsimp [K]; norm_cast
  rw [hKcast] at hb hmass
  have hA' := ((div_lt_iff₀ hδ).mp hA).le
  have hAK : (A : ℝ) ≤ k := by exact_mod_cast (show A ≤ k by dsimp [k]; omega)
  have hl : 4 * c ^ 2 + 20 * c ≤ (k : ℝ) * δ :=
    hA'.trans (mul_le_mul_of_nonneg_right hAK hδ.le)
  have hprod := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ (n : ℝ) * (k : ℝ) by positivity)
  dsimp [δ] at hprod
  nlinarith only [hb, hmass, hend, herr, herr', hlin, hprod]

end GoldenNormality.BinaryComplement
