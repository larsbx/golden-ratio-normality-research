import GoldenNormality.BinaryPartitionCarry
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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
  have hadd := integral_add_adjacent_intervals (a := (-1 : ℝ)) (b := 0) (c := 1)
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

private theorem sqrt_le_sqrt_add_one (a b : ℝ) (hb : 0 ≤ b) (hab : a ≤ b + 1) :
    Real.sqrt a ≤ Real.sqrt b + 1 := by
  apply Real.sqrt_le_iff.mpr
  have h := Real.sqrt_nonneg b
  exact ⟨by linarith, by nlinarith only [hab, h, Real.sq_sqrt hb]⟩

/-- The upper rectangular sum differs from the quarter-circle area by at most
one unit of height times its radius. -/
theorem sqrt_checkpoint_sum_le (K : ℕ) :
    (∑ i ∈ Finset.range K, (Real.sqrt ((i : ℝ) + 1) - Real.sqrt i) *
      Real.sqrt (K - i : ℕ)) ≤ (K : ℝ) * Real.pi / 4 + Real.sqrt K := by
  let f := fun x : ℝ => Real.sqrt ((K : ℝ) - x ^ 2) + 1
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
          nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hx0 (Real.sqrt_nonneg _))]
        have hKm : (m : ℝ) + 1 ≤ K := by exact_mod_cast hm
        have hcast : ((K - m : ℕ) : ℝ) = (K : ℝ) - m := Nat.cast_sub (by omega)
        rw [hcast]
        exact sqrt_le_sqrt_add_one _ _ (by linarith) (by linarith)
      have hadd := integral_add_adjacent_intervals (a := (0 : ℝ))
        (b := Real.sqrt (m : ℝ)) (c := Real.sqrt ((m : ℝ) + 1))
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
      push_cast
      rw [Finset.sum_range_succ, ← hadd]
      exact add_le_add hprev hpiece
  have h := hsum K le_rfl
  dsimp [f] at h
  have hs : Continuous (fun x : ℝ => Real.sqrt ((K : ℝ) - x ^ 2)) := by fun_prop
  rw [integral_add (hs.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    quarterCircleIntegral_scaled, integral_const] at h
  simpa [smul_eq_mul] using h

/-- A square-root envelope on all checkpoints must meet the semicircle budget. -/
theorem original_zero_count_semicircle_envelope (K n : ℕ) (hN : 2 ≤ K * n)
    (c : ℝ) (hc : 0 ≤ c)
    (hcap : ∀ i ≤ K, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤
      c * Real.sqrt ((i * n : ℕ) : ℝ)) :
    (K * n : ℝ) ≤ 2 * c ^ 2 * n * ((K : ℝ) * Real.pi / 4 + Real.sqrt K) +
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
  have h := mul_le_mul_of_nonneg_left (sqrt_checkpoint_sum_le K) (sq_nonneg r)
  have hsq : r ^ 2 = c ^ 2 * n := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq] at hb h
  dsimp [g, r] at hb
  linarith only [hb, h]

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
  have hK : 1 ≤ K := by dsimp [K]; positivity
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
    have hmul := Nat.mul_le_mul_right n hi'
    dsimp [n] at hmul
    omega
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

end GoldenNormality.BinaryComplement
