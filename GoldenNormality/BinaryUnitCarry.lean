import GoldenNormality.BinarySemicircleCarry
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic

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

/-- Reversing the indices cancels every off-diagonal product modulo two. -/
theorem convolutionCoefficient_mod_two (n : ℕ) :
    (convolutionCoefficient n : ZMod 2) = (diagonalIndicator n : ZMod 2) := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  let flip := fun i : ℕ => n - 1 - i
  let w := fun i : ℕ => (digit i : ZMod 2) * (digit (flip i) : ZMod 2)
  have hoff : (∑ i ∈ (Finset.range n).filter (fun i => flip i ≠ i), w i) = 0 := by
    apply Finset.sum_involution (fun i _ => flip i)
    · intro i hi
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      have he : flip (flip i) = i := by dsimp [flip]; omega
      simp only [w, he, mul_comm (digit (flip i) : ZMod 2) (digit i : ZMod 2)]
      rw [← two_mul, htwo, zero_mul]
    · intro i hi _
      exact (Finset.mem_filter.mp hi).2
    · intro i hi
      obtain ⟨hi', hne⟩ := Finset.mem_filter.mp hi
      have hi'' := Finset.mem_range.mp hi'
      apply Finset.mem_filter.mpr
      dsimp [flip] at *
      exact ⟨Finset.mem_range.mpr (by omega), by omega⟩
    · intro i hi
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      dsimp [flip]
      omega
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range n)
    (fun i => flip i ≠ i) w
  rw [hoff, zero_add] at hsplit
  unfold convolutionCoefficient
  simp only [Int.cast_sum, Int.cast_mul]
  change (∑ i ∈ Finset.range n, w i) = _
  rw [← hsplit]
  by_cases ho : n % 2 = 1
  · have hset : ((Finset.range n).filter (fun i => ¬ flip i ≠ i)) = {n / 2} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, not_not, flip]
      omega
    have he : flip (n / 2) = n / 2 := by dsimp [flip]; omega
    rw [hset, Finset.sum_singleton]
    have hd : digit (n / 2) = 0 ∨ digit (n / 2) = 1 := by
      have := digit_range (n / 2)
      omega
    rcases hd with hd | hd <;> simp [w, he, diagonalIndicator, ho, hd]
  · have hset : ((Finset.range n).filter (fun i => ¬ flip i ≠ i)) = ∅ := by
      ext i
      constructor
      · intro hi
        have hm := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
        have he : flip i = i := Classical.not_not.mp (Finset.mem_filter.mp hi).2
        dsimp [flip] at he
        exact (ho (by omega)).elim
      · intro hi
        exact (Finset.notMem_empty i hi).elim
    rw [hset, Finset.sum_empty]
    simp [diagonalIndicator, ho]

private theorem unitCarry_next_le (n : ℕ) :
    unitCarryIndicator (n + 1) ≤ digit n + diagonalIndicator n := by
  have hd := digit_range n
  have hdiag : 0 ≤ diagonalIndicator n := by
    unfold diagonalIndicator
    split
    · exact (digit_range _).1
    · exact le_rfl
  unfold unitCarryIndicator
  split
  · rename_i hc
    by_cases hz : digit n = 0
    · have hr := carry_recurrence n
      unfold signedCoefficient at hr
      rw [hc, hz, mul_zero, sub_zero] at hr
      have htwo : (2 : ZMod 2) = 0 := by decide
      have hcast' : (2 : ZMod 2) * (carry n : ZMod 2) =
          1 + (convolutionCoefficient n : ZMod 2) := by
        have hh := congrArg (fun x : ℤ => (x : ZMod 2)) hr
        simpa only [Int.cast_mul, Int.cast_add, Int.cast_ofNat, Int.cast_one] using hh
      rw [htwo, zero_mul] at hcast'
      have hpar := convolutionCoefficient_mod_two n
      have hodd : (diagonalIndicator n : ZMod 2) = 1 := by
        rw [← hpar]
        have he := congrArg (fun x : ZMod 2 => x - 1) hcast'
        have hn : (0 : ZMod 2) - 1 = 1 := by decide
        simpa only [hn, add_comm (1 : ZMod 2), add_sub_cancel_right] using he.symm
      have h01 : diagonalIndicator n = 0 ∨ diagonalIndicator n = 1 := by
        unfold diagonalIndicator
        split
        · have := digit_range (n / 2)
          omega
        · exact Or.inl rfl
      rcases h01 with h | h
      · simp [h] at hodd
      · simp [hz, h]
    · omega
  · omega

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

private theorem diagonal_sum_eq (N : ℕ) :
    (∑ i ∈ Finset.range N, diagonalIndicator i) = ∑ i ∈ Finset.range (N / 2), digit i := by
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
  rcases hcases with hk | hk
  · rw [hk, hpair, show 2 * k / 2 = k by omega]
  · rw [hk, Finset.sum_range_succ, hpair]
    simp [diagonalIndicator, show (2 * k + 1) / 2 = k by omega]

private theorem diagonal_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, diagonalIndicator i) ≤ ∑ i ∈ Finset.range N, digit i := by
  rw [diagonal_sum_eq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega)) (fun i _ _ => (digit_range i).1)

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

private theorem twice_positive_count_le_mass_add_units (N : ℕ) :
    2 * (∑ i ∈ Finset.range N, positiveCarryIndicator i) ≤
      (∑ i ∈ Finset.range N, positiveCarry i) + ∑ i ∈ Finset.range N, unitCarryIndicator i := by
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
  exact hmass

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
  have hmass := twice_positive_count_le_mass_add_units N
  have hu := twice_unitCarry_sum_le N
  have hg := prefix_le_positive_count_and_zeros N
  omega

/-- The incoming unit carry charge retains the endpoint and the exact
half-prefix diagonal count. -/
theorem unitCarry_sum_add_endpoint_le (N : ℕ) :
    (∑ i ∈ Finset.range N, unitCarryIndicator i) + unitCarryIndicator N ≤
      (GoldenNormality.occurrences 2 1 0 N : ℤ) +
        (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ) := by
  rw [← digit_sum_eq_original_zeros, ← digit_sum_eq_original_zeros, ← diagonal_sum_eq]
  induction N with
  | zero => simp [unitCarryIndicator]
  | succ N ih =>
    simp only [Finset.sum_range_succ] at *
    have h := unitCarry_next_le N
    omega

/-- Every size-one carry can be charged to the preceding digit or its
diagonal product. The origin carry is excluded because it is negative. -/
theorem unitCarry_sum_le (N : ℕ) :
    (∑ i ∈ Finset.range N, unitCarryIndicator i) ≤
      2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  have hn : 0 ≤ unitCarryIndicator N := by unfold unitCarryIndicator; split <;> omega
  have hd := diagonal_sum_le N
  rw [diagonal_sum_eq, digit_sum_eq_original_zeros, digit_sum_eq_original_zeros] at hd
  have h := unitCarry_sum_add_endpoint_le N
  omega

/-- The parity, gap and positive-carry budgets with the terminal carries
and the simultaneous digit charge retained. -/
theorem original_zero_count_parity_carry_budget (N : ℕ) :
    (N : ℤ) + 3 * (∑ i ∈ Finset.range N, digit i * positiveCarryIndicator i) +
      unitCarryIndicator N ≤
      (∑ i ∈ Finset.range N, convolutionCoefficient i) + positiveCarry N +
      5 * (GoldenNormality.occurrences 2 1 0 N : ℤ) +
      (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ) + 1 := by
  have hc := positiveCarry_sum_add_digits_le 0 N
  have hzero : positiveCarry 0 = 0 := by simp [positiveCarry]
  simp only [Nat.zero_add, hzero, add_zero] at hc
  have hmass := twice_positive_count_le_mass_add_units N
  have hu := unitCarry_sum_add_endpoint_le N
  have hg := prefix_le_positive_count_and_zeros N
  omega

/-- The same budget with the terminal positive carry bounded by the zero count. -/
theorem original_zero_count_parity_overlap_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) + 3 * (∑ i ∈ Finset.range N, digit i * positiveCarryIndicator i) +
      unitCarryIndicator N ≤
      (∑ i ∈ Finset.range N, convolutionCoefficient i) +
      6 * (GoldenNormality.occurrences 2 1 0 N : ℤ) +
      (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ) := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have h := original_zero_count_parity_carry_budget N
  omega

/-- The gap count and the unit-carry parity restriction give a lower budget
for truncated convolution mass. -/
theorem original_zero_count_parity_carry_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) ≤ (∑ i ∈ Finset.range N, convolutionCoefficient i) +
      7 * (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  have h := original_zero_count_parity_overlap_bound N hN
  have hd := diagonal_sum_le N
  rw [diagonal_sum_eq, digit_sum_eq_original_zeros, digit_sum_eq_original_zeros] at hd
  have ho : 0 ≤ ∑ i ∈ Finset.range N, digit i * positiveCarryIndicator i :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (digit_range i).1 (le_min (by decide) (le_max_right _ _))
  have hu : 0 ≤ unitCarryIndicator N := by unfold unitCarryIndicator; split <;> omega
  omega

private theorem zero_count_exceeds_from_pair_budget (leading linear : ℝ) (hl₀ : 0 ≤ linear)
    (hcarry : ∀ N : ℕ, 2 ≤ N → leading * (N : ℝ) ≤
      4 * (∑ i ∈ Finset.range N, (convolutionCoefficient i : ℝ)) +
        linear * (GoldenNormality.occurrences 2 1 0 N : ℝ))
    (c : ℝ) (hc : 0 ≤ c) (hcritical : Real.pi * c ^ 2 < leading) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let δ := leading - Real.pi * c ^ 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA⟩ := exists_nat_gt ((4 * c ^ 2 + linear * c) / δ)
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
  have hb := hcarry (K * n) hN
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
  have hend' := mul_le_mul_of_nonneg_left hend hl₀
  have hlin : linear * c * (k : ℝ) * Real.sqrt n ≤ linear * c * (k : ℝ) * n := mul_le_mul_of_nonneg_left hnroot
    (show 0 ≤ linear * c * (k : ℝ) by positivity)
  have hKcast : (K : ℝ) = (k : ℝ) ^ 2 := by dsimp [K]; norm_cast
  rw [hKcast] at hb hmass
  have hAK : (A : ℝ) ≤ k := by exact_mod_cast (show A ≤ k by dsimp [k]; omega)
  have hm : (∑ i ∈ Finset.range (K * n), (convolutionCoefficient i : ℝ)) ≤
      c ^ 2 * n * (((k : ℝ) ^ 2 + 1) * Real.pi / 4) := hmass
  have hk' : (0 : ℝ) < k := by linarith only [hk]
  have hmargin : (4 * c ^ 2 + linear * c) * ((n : ℝ) * k) <
      ((k : ℝ) * δ) * ((n : ℝ) * k) := by
    apply mul_lt_mul_of_pos_right _ (mul_pos (by exact_mod_cast (show 0 < n by omega)) hk')
    exact ((div_lt_iff₀ hδ).mp hA).trans_le
      (mul_le_mul_of_nonneg_right hAK hδ.le)
  dsimp [δ] at hmargin
  nlinarith only [hb, hm, hend', herr, herr', hlin, hmargin]

/-- At arbitrarily late prefixes, the normalized zero count exceeds
every nonnegative constant below `√(3/π)`. -/
theorem original_zero_count_exceeds_of_pi_mul_sq_lt_three (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 3) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  apply zero_count_exceeds_from_pair_budget 3 20 (by norm_num) _ c hc hcritical M
  intro N hN
  have h := Int.cast_le (R := ℝ).mpr (original_zero_count_unit_carry_bound N hN)
  push_cast at h
  linarith only [h]

/-- The full parity restriction raises the limsup lower bound to `2 / √π`. -/
theorem original_zero_count_exceeds_of_pi_mul_sq_lt_four (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 4) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  apply zero_count_exceeds_from_pair_budget 4 28 (by norm_num) _ c hc hcritical M
  intro N hN
  have h := Int.cast_le (R := ℝ).mpr (original_zero_count_parity_carry_bound N hN)
  push_cast at h
  linarith only [h]

/-- The parity budget gives an all-prefix quadratic bound on the actual zero count. -/
theorem original_zero_count_parity_quadratic_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) ≤ (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 +
      7 * (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  have hp := original_zero_count_parity_carry_bound N hN
  have hs := convolution_sum_le_square N
  omega

/-- Every prefix past the given threshold exceeds the square-root envelope.
In particular the liminf of the normalized zero count is at least one. -/
theorem original_zero_count_parity_above (N : ℕ) (hN : 2 ≤ N) (c : ℝ) (hc : 0 ≤ c)
    (hmargin : 7 * c < (1 - c ^ 2) * Real.sqrt (N : ℝ)) :
    c * Real.sqrt (N : ℝ) < (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let t := Real.sqrt (N : ℝ)
  let z : ℝ := GoldenNormality.occurrences 2 1 0 N
  have ht : 0 < t := Real.sqrt_pos_of_pos (by exact_mod_cast (show 0 < N by omega))
  have ht2 : t ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg _)
  have hz : 0 ≤ z := Nat.cast_nonneg _
  have hs : (N : ℝ) ≤ z ^ 2 + 7 * z := by
    dsimp only [z]
    exact_mod_cast original_zero_count_parity_quadratic_bound N hN
  by_contra! h
  change z ≤ c * t at h
  have hsq := (sq_le_sq₀ hz (mul_nonneg hc ht.le)).mpr h
  have hm := mul_lt_mul_of_pos_right hmargin ht
  change 7 * c * t < ((1 - c ^ 2) * t) * t at hm
  nlinarith only [hs, h, hsq, ht2, hm]

/-- An exact threshold for the all-prefix coefficient `0.99`. -/
theorem original_zero_count_parity_above_99 (N : ℕ) (hN : 122500 ≤ N) :
    (99 / 100 : ℝ) * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  apply original_zero_count_parity_above N (by omega) _ (by norm_num)
  have ht : (350 : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hN)
  linarith only [ht]

/-- A strict finite checkpoint guarantee from the parity carry budget. -/
theorem original_zero_count_parity_window (K n : ℕ) (hN : 2 ≤ K * n) (c : ℝ) (hc : 0 ≤ c)
    (hmargin : 7 * c * Real.sqrt (K : ℝ) <
      ((K : ℝ) - c ^ 2 * (((K : ℝ) + 1) * Real.pi / 4)) * Real.sqrt (n : ℝ)) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ K ∧ c * Real.sqrt ((i * n : ℕ) : ℝ) <
      (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  by_contra! h
  have hcap : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
      c * Real.sqrt ((i * n : ℕ) : ℝ) := by
    intro i hi
    by_cases hz : i = 0
    · simp [hz, GoldenNormality.occurrences_zero]
    · exact h i (by omega) hi
  have hmass := convolution_sum_le_succ_area_envelope K n c hc hcap
  have hb := Int.cast_le (R := ℝ).mpr (original_zero_count_parity_carry_bound (K * n) hN)
  push_cast at hb
  have hend := hcap K le_rfl
  push_cast at hend
  rw [Real.sqrt_mul (Nat.cast_nonneg K)] at hend
  have hn : 0 < n := by
    by_contra! hz
    simp [show n = 0 by omega] at hN
  have ht : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hn)
  have hm := mul_lt_mul_of_pos_right hmargin ht
  have hsq := Real.sq_sqrt (Nat.cast_nonneg n)
  nlinarith only [hb, hmass, hend, hm,
    congrArg (fun x : ℝ => ((K : ℝ) - c ^ 2 * (((K : ℝ) + 1) * Real.pi / 4)) * x) hsq]

/-- Every window of 1024 checkpoints of width at least 2500 contains
a prefix with more than `1.125 * √N` original zeros. -/
theorem original_zero_count_parity_window_nine_eighths (n : ℕ) (hn : 2500 ≤ n) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 1024 ∧
      (9 / 8 : ℝ) * Real.sqrt ((i * n : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  apply original_zero_count_parity_window 1024 n (by omega) _ (by norm_num)
  have hk : Real.sqrt (↑(1024 : ℕ) : ℝ) = 32 := by
    rw [show (↑(1024 : ℕ) : ℝ) = 32 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hk]
  let t := Real.sqrt (n : ℝ)
  have ht : (50 : ℝ) ≤ t := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have ht₀ : 0 ≤ t := by linarith
  have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_d4.le ht₀
  change 7 * (9 / 8 : ℝ) * 32 <
    (1024 - (9 / 8 : ℝ) ^ 2 * ((1024 + 1) * Real.pi / 4)) * t
  nlinarith only [ht, hπ]

end GoldenNormality.BinaryComplement
