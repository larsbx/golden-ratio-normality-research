import GoldenNormality.BinaryPartitionCarry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

/-! A semicircle estimate for every equal-width partition. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators
open intervalIntegral

private theorem quarterCircleIntegral :
    (∫ x in (0 : ℝ)..1, Real.sqrt (1 - x ^ 2)) = Real.pi / 4 := by
  let f := fun x : ℝ => Real.sqrt (1 - x ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hneg : (∫ x in (-1 : ℝ)..0, f x) = ∫ x in (0 : ℝ)..1, f x := by
    have h := integral_comp_neg (a := (0 : ℝ)) (b := 1) f
    simpa only [neg_zero, f, neg_sq] using h.symm
  have hadd := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (a := (-1 : ℝ)) (b := 0) (c := 1)
    (hf.intervalIntegrable (-1) 0) (hf.intervalIntegrable 0 1)
  rw [hneg] at hadd
  change _ + _ = (∫ x in (-1 : ℝ)..1, Real.sqrt (1 - x ^ 2)) at hadd
  rw [integral_sqrt_one_sub_sq] at hadd
  linarith only [hadd]

private theorem quarterCircleIntegral_scaled (K : ℕ) :
    (∫ x in (0 : ℝ)..Real.sqrt K, Real.sqrt ((K : ℝ) - x ^ 2)) =
      (K : ℝ) * Real.pi / 4 := by
  by_cases hK : K = 0
  · simp [hK]
  let r := Real.sqrt (K : ℝ)
  have hr : 0 < r := Real.sqrt_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hK)
  have hr2 : r ^ 2 = (K : ℝ) := Real.sq_sqrt (Nat.cast_nonneg K)
  let f := fun x : ℝ => Real.sqrt ((K : ℝ) - x ^ 2)
  have he : (fun x : ℝ => f (r * x)) = fun x => r * Real.sqrt (1 - x ^ 2) := by
    funext x
    dsimp [f]
    rw [show (K : ℝ) - (r * x) ^ 2 = r ^ 2 * (1 - x ^ 2) by rw [← hr2]; ring,
      Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le]
  have h := integral_comp_mul_left (a := (0 : ℝ)) (b := 1) f hr.ne'
  rw [he, integral_const_mul, quarterCircleIntegral, mul_zero, mul_one, smul_eq_mul] at h
  change (∫ x in (0 : ℝ)..r, f x) = _
  have h' := congrArg (fun x : ℝ => r * x) h
  change r * (r * (Real.pi / 4)) = r * (r⁻¹ * _) at h'
  rw [← mul_assoc r r⁻¹, mul_inv_cancel₀ hr.ne', one_mul] at h'
  rw [← h', ← hr2]
  ring

/-- Every checkpoint rectangle lies under the quarter circle with squared
radius `K + 1`. This increases the area by only `π / 4`. -/
theorem sqrt_checkpoint_sum_le_succ_area (K : ℕ) :
    (∑ i ∈ Finset.range K, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
      Real.sqrt (K - i : ℕ)) ≤ ((K : ℝ) + 1) * Real.pi / 4 := by
  let f := fun x : ℝ => Real.sqrt ((K : ℝ) + 1 - x ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hsum : ∀ m ≤ K,
      (∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
        Real.sqrt (K - i : ℕ)) ≤ ∫ x in (0 : ℝ)..Real.sqrt m, f x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hpiece : (Real.sqrt ((m : ℝ) + 1) - Real.sqrt m) * Real.sqrt (K - m : ℕ) ≤
          ∫ x in Real.sqrt (m : ℝ)..Real.sqrt ((m : ℝ) + 1), f x := by
        rw [← smul_eq_mul, ← integral_const]
        apply integral_mono_on hle (continuous_const.intervalIntegrable _ _)
          (hf.intervalIntegrable _ _)
        intro x hx
        have hx0 : 0 ≤ x := (Real.sqrt_nonneg _).trans hx.1
        have hx2 : x ^ 2 ≤ (m : ℝ) + 1 := by
          have he := Real.sq_sqrt (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity)
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hx0 (Real.sqrt_nonneg ((m : ℝ) + 1)))]
        have hcast : ((K - m : ℕ) : ℝ) = (K : ℝ) - m := Nat.cast_sub (by omega)
        rw [hcast]
        apply Real.sqrt_le_sqrt
        linarith only [hx2]
      have hadd := integral_add_adjacent_intervals (μ := MeasureTheory.volume) (a := (0 : ℝ))
        (b := Real.sqrt (m : ℝ)) (c := Real.sqrt ((m : ℝ) + 1))
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
      push_cast
      rw [Finset.sum_range_succ, ← hadd]
      exact add_le_add hprev hpiece
  have hle : Real.sqrt (K : ℝ) ≤ Real.sqrt ((K + 1 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  have htail : 0 ≤ ∫ x in Real.sqrt (K : ℝ)..Real.sqrt ((K + 1 : ℕ) : ℝ), f x :=
    integral_nonneg_of_forall hle (fun x => Real.sqrt_nonneg _)
  have htotal : (∫ x in (0 : ℝ)..Real.sqrt ((K + 1 : ℕ) : ℝ), f x) =
      ((K : ℝ) + 1) * Real.pi / 4 := by
    simpa only [Nat.cast_add, Nat.cast_one, f] using quarterCircleIntegral_scaled (K + 1)
  have hadd := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hf.intervalIntegrable (0 : ℝ) (Real.sqrt (K : ℝ)))
    (hf.intervalIntegrable (Real.sqrt (K : ℝ)) (Real.sqrt ((K + 1 : ℕ) : ℝ)))
  linarith only [hsum K le_rfl, htail, htotal, hadd]

/-- The same rectangles cover the quarter circle of squared radius `K`. -/
theorem le_sqrt_checkpoint_sum (K : ℕ) :
    (K : ℝ) * Real.pi / 4 ≤
      ∑ i ∈ Finset.range K, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
        Real.sqrt (K - i : ℕ) := by
  let f := fun x : ℝ => Real.sqrt ((K : ℝ) - x ^ 2)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hsum : ∀ m ≤ K, (∫ x in (0 : ℝ)..Real.sqrt m, f x) ≤
      ∑ i ∈ Finset.range m, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
        Real.sqrt (K - i : ℕ) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      have hpiece : (∫ x in Real.sqrt (m : ℝ)..Real.sqrt ((m : ℝ) + 1), f x) ≤
          (Real.sqrt ((m : ℝ) + 1) - Real.sqrt m) * Real.sqrt (K - m : ℕ) := by
        rw [← smul_eq_mul, ← integral_const]
        apply integral_mono_on hle (hf.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _)
        intro x hx
        have hroot : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
        have hx0 : 0 ≤ x := hroot.trans hx.1
        have hx2 : (m : ℝ) ≤ x ^ 2 := by
          rw [← Real.sq_sqrt (Nat.cast_nonneg m)]
          exact (sq_le_sq₀ hroot hx0).mpr hx.1
        have hcast : ((K - m : ℕ) : ℝ) = (K : ℝ) - m := Nat.cast_sub (by omega)
        rw [hcast]
        apply Real.sqrt_le_sqrt
        linarith only [hx2]
      have hadd := integral_add_adjacent_intervals (μ := MeasureTheory.volume)
        (b := Real.sqrt (m : ℝ)) (c := Real.sqrt ((m : ℝ) + 1))
        (hf.intervalIntegrable (0 : ℝ) _) (hf.intervalIntegrable _ _)
      push_cast
      rw [Finset.sum_range_succ, ← hadd]
      exact add_le_add hprev hpiece
  have h := hsum K le_rfl
  dsimp only [f] at h
  rwa [quarterCircleIntegral_scaled] at h

open Filter
open scoped Topology

/-- The normalized rectangular sum converges to the quarter-circle constant. -/
theorem tendsto_sqrt_checkpoint_average :
    Tendsto (fun K : ℕ =>
      (∑ i ∈ Finset.range K, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
        Real.sqrt (K - i : ℕ)) / (K : ℝ)) atTop (𝓝 (Real.pi / 4)) := by
  have hupper : Tendsto (fun K : ℕ => Real.pi / 4 + (Real.pi / 4) / (K : ℝ))
      atTop (𝓝 (Real.pi / 4)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := Real.pi / 4)).add
        (tendsto_const_div_atTop_nhds_zero_nat (Real.pi / 4))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
    have hpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    apply (le_div_iff₀ hpos).mpr
    rw [div_mul_eq_mul_div, mul_comm Real.pi (K : ℝ)]
    exact le_sqrt_checkpoint_sum K
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
    have hpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ ((K : ℝ) + 1) * Real.pi / 4 := sqrt_checkpoint_sum_le_succ_area K
      _ = (Real.pi / 4 + (Real.pi / 4) / (K : ℝ)) * (K : ℝ) := by
        field_simp

/-- The original radius-error estimate follows from the constant area error. -/
theorem sqrt_checkpoint_sum_le (K : ℕ) :
    (∑ i ∈ Finset.range K, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
      Real.sqrt (K - i : ℕ)) ≤ (K : ℝ) * Real.pi / 4 + Real.sqrt K := by
  by_cases hK : K = 0
  · simp [hK]
  have hk : (1 : ℝ) ≤ Real.sqrt K :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast (show 1 ^ 2 ≤ K by omega))
  linarith only [sqrt_checkpoint_sum_le_succ_area K, Real.pi_le_four, hk]

/-- A square-root envelope on all checkpoints must meet the semicircle budget. -/
theorem original_zero_count_succ_area_envelope (K n : ℕ) (hN : 2 ≤ K * n)
    (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
      c * Real.sqrt ((i * n : ℕ) : ℝ)) :
    (K * n : ℝ) ≤ 2 * c ^ 2 * n * (((K : ℝ) + 1) * Real.pi / 4) +
      6 * c * Real.sqrt n * Real.sqrt K - 1 := by
  let r := c * Real.sqrt (n : ℝ)
  have hr : 0 ≤ r := mul_nonneg hc (Real.sqrt_nonneg _)
  let g := fun i : ℕ => r * Real.sqrt (i : ℝ)
  have hbound : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤ g i := by
    intro i hi
    have h := hcap i hi
    push_cast at h
    rw [Real.sqrt_mul (Nat.cast_nonneg i)] at h
    convert h using 1
    dsimp [g, r]
    ring
  have hb := original_zero_count_partition_envelope K n hN g (by simp [g])
    (fun i j h => mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast h)) hr) hbound
  have hsum : (∑ i ∈ Finset.range K, (g (i + 1) - g i) * g (K - i)) =
      r ^ 2 * ∑ i ∈ Finset.range K,
        (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) * Real.sqrt (K - i : ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g]
    push_cast only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hsum] at hb
  have h := mul_le_mul_of_nonneg_left (sqrt_checkpoint_sum_le_succ_area K) (sq_nonneg r)
  have hsq : r ^ 2 = c ^ 2 * n := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq] at hb h
  dsimp [g, r] at hb
  linarith only [hb, h]

/-- A square-root envelope on all checkpoints must meet the semicircle budget. -/
theorem original_zero_count_semicircle_envelope (K n : ℕ) (hN : 2 ≤ K * n)
    (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
      c * Real.sqrt ((i * n : ℕ) : ℝ)) :
    (K * n : ℝ) ≤ 2 * c ^ 2 * n * ((K : ℝ) * Real.pi / 4 + Real.sqrt K) +
      6 * c * Real.sqrt n * Real.sqrt K - 1 := by
  have h := original_zero_count_succ_area_envelope K n hN c hc hcap
  have hK : K ≠ 0 := by intro hz; simp [hz] at hN
  have hk : (1 : ℝ) ≤ Real.sqrt K :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast (show 1 ^ 2 ≤ K by omega))
  have harea : ((K : ℝ) + 1) * Real.pi / 4 ≤ (K : ℝ) * Real.pi / 4 + Real.sqrt K := by
    linarith only [Real.pi_le_four, hk]
  have hmul := mul_le_mul_of_nonneg_left harea
    (show 0 ≤ 2 * c ^ 2 * (n : ℝ) by positivity)
  linarith only [h, hmul]

/-- Every smaller nonnegative constant than `√(2/π)` is exceeded at
arbitrarily late prefixes of the actual binary zero count. -/
theorem original_zero_count_exceeds_of_pi_mul_sq_lt (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 2) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let δ := 1 - Real.pi * c ^ 2 / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA⟩ := exists_nat_gt ((2 * c ^ 2 + 6 * c) / δ)
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
  have hb := original_zero_count_semicircle_envelope K n hN c hc hcap
  have hKcast : (K : ℝ) = (k : ℝ) ^ 2 := by dsimp [K]; norm_cast
  rw [hsqrt, hKcast] at hb
  have hlin := mul_le_mul_of_nonneg_left hnroot
    (show 0 ≤ 6 * c * (k : ℝ) by positivity)
  have hA' := ((div_lt_iff₀ hδ).mp hA).le
  have hAK : (A : ℝ) ≤ k := by exact_mod_cast (show A ≤ k by dsimp [k]; omega)
  have hl : 2 * c ^ 2 + 6 * c ≤ (k : ℝ) * δ :=
    hA'.trans (mul_le_mul_of_nonneg_right hAK hδ.le)
  have hprod := mul_le_mul_of_nonneg_right hl
    (show 0 ≤ (n : ℝ) * (k : ℝ) by positivity)
  dsimp [δ] at hprod
  nlinarith only [hb, hlin, hprod]

/-- A finite checkpoint guarantee near the limiting constant. -/
theorem original_zero_count_succ_area_window (n : ℕ) (hn : 65536 ≤ n) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 16384 ∧
      (3989 / 5000 : ℝ) * Real.sqrt ((i * n : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  by_contra! h
  have hcap (i : ℕ) (hi : i ≤ 16384) :
      (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
        (3989 / 5000 : ℝ) * Real.sqrt ((i * n : ℕ) : ℝ) := by
    by_cases hz : i = 0
    · simp [hz, GoldenNormality.occurrences_zero]
    exact h i (by omega) hi
  have hb := original_zero_count_succ_area_envelope 16384 n (by omega) _ (by norm_num) hcap
  have hs : Real.sqrt (↑(16384 : ℕ) : ℝ) = 128 := by
    rw [show (↑(16384 : ℕ) : ℝ) = 128 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs] at hb
  push_cast at hb
  let t := Real.sqrt (n : ℝ)
  have ht : (256 : ℝ) ≤ t := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have ht₀ : 0 ≤ t := Real.sqrt_nonneg _
  have hπ := mul_le_mul_of_nonneg_right Real.pi_lt_d4.le (show 0 ≤ (n : ℝ) by positivity)
  have hsq : (n : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg n)).symm
  change 16384 * (n : ℝ) ≤
    2 * (3989 / 5000 : ℝ) ^ 2 * n * ((16384 + 1) * Real.pi / 4) +
      6 * (3989 / 5000 : ℝ) * t * 128 - 1 at hb
  rw [hsq] at hb hπ
  have hprod := mul_nonneg (sub_nonneg.mpr ht) ht₀
  nlinarith only [hb, hπ, hprod, ht₀]

end GoldenNormality.BinaryComplement
