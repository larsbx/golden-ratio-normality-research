import GoldenNormality.BinaryGapTransfer
import RidoutBridge.RidoutSpecialization

/-!
Golden-ratio application of Ridout's theorem at the pinned external revision.
The imported carry/count definitions are the exact root-project sources.
-/

namespace GoldenNormality.RidoutBridge

theorem algebraic_alpha : IsAlgebraic ℚ GoldenNormality.alpha := by
  refine ⟨(Polynomial.X : Polynomial ℚ) ^ 2 + Polynomial.X - 1, ?_, ?_⟩
  · intro hzero
    have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff 2) hzero
    norm_num [Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one] at hcoeff
  · rw [Polynomial.aeval_sub, Polynomial.aeval_add,
      Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one]
    exact sub_eq_zero.mpr GoldenNormality.alpha_quadratic

/-- Ridout separates every fixed nonzero integer multiple of the actual source
from all integer numerators at sufficiently late dyadic scales. -/
theorem fixedMultiplier_eventualDyadicSeparation (h : ℤ) (hh : h ≠ 0)
    (B : ℕ) (hB : 0 < B) : ∃ M : ℕ, ∀ (n : ℕ) (p : ℤ), M ≤ n →
      1 ≤ |(2 : ℝ) ^ n * ((h : ℝ) * GoldenNormality.alpha) - (p : ℝ)| ^ B * (2 : ℝ) ^ n := by
  let x : ℝ := (h : ℝ) * GoldenNormality.alpha
  let ξ := Int.fract x
  have hirr : Irrational x := BinaryDyadicOrbit.irrational_alpha.intCast_mul hh
  have hξirr : Irrational ξ := hirr.sub_intCast ⌊x⌋
  have hξalg : IsAlgebraic ℚ ξ :=
    ((isAlgebraic_intCast (R := ℚ) (A := ℝ) h).mul algebraic_alpha).sub
      (isAlgebraic_intCast (R := ℚ) (A := ℝ) ⌊x⌋)
  have hξpos : 0 < ξ := sub_pos.mpr ((Int.floor_le x).lt_of_ne (Ne.symm (hirr.ne_int ⌊x⌋)))
  obtain ⟨M, hM⟩ := eventualDyadicSeparation_of_finite_candidates
    hξirr hξpos (Int.fract_lt_one x) (fun _ hK => finite_dyadicCandidates hξalg hK) B hB
  refine ⟨M, fun n p hn => ?_⟩
  have he : (2 : ℝ) ^ n * ξ - ((p - (2 : ℤ) ^ n * ⌊x⌋ : ℤ) : ℝ) =
      (2 : ℝ) ^ n * x - (p : ℝ) := by
    simp only [ξ, Int.fract, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    ring
  rw [← he]
  exact hM n hn _

/-- For any fixed positive lag, late orbit differences avoid every integer
at the scale of Ridout's all-numerator estimate. -/
theorem fixedLag_eventual_separation (d : ℕ) (hd : 0 < d) (B : ℕ) (hB : 0 < B) :
    ∃ M : ℕ, ∀ (n : ℕ) (p : ℤ), M ≤ n →
      1 ≤ |BinaryDyadicOrbit.point (n + d) - BinaryDyadicOrbit.point n - (p : ℝ)| ^ B *
        (2 : ℝ) ^ n := by
  let h : ℤ := 2 ^ d - 1
  have hcast : (h : ℝ) = (2 : ℝ) ^ d - 1 := by simp [h]
  have hh : h ≠ 0 := by
    have hp : (1 : ℝ) < 2 ^ d := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hd)
    exact_mod_cast (show (h : ℝ) ≠ 0 by rw [hcast]; exact sub_ne_zero.mpr hp.ne')
  obtain ⟨M, hM⟩ := fixedMultiplier_eventualDyadicSeparation h hh B hB
  refine ⟨M, fun n p hn => ?_⟩
  have he :
      (2 : ℝ) ^ n * ((h : ℝ) * alpha) -
          ((p + scaledFloor 2 (n + d) - scaledFloor 2 n : ℤ) : ℝ) =
        BinaryDyadicOrbit.point (n + d) - BinaryDyadicOrbit.point n - (p : ℝ) := by
    rw [hcast]
    simp only [BinaryDyadicOrbit.point, scaledFloor, Int.fract, Int.cast_sub, Int.cast_add,
      Nat.cast_ofNat]
    rw [pow_add]
    ring
  rw [← he]
  exact hM n _ hn

/-- At a fixed positive lag, repetitions at sufficiently late starts have
sublinear width. The threshold is uniform over the tested block width. -/
theorem fixedLag_repeatedBlock_mul_lt (d : ℕ) (hd : 0 < d) (B : ℕ) (hB : 0 < B) :
    ∃ M : ℕ, ∀ (n k : ℕ), M ≤ n → blockValue 2 (n + d) k = blockValue 2 n k →
      B * k < n := by
  obtain ⟨M, hM⟩ := fixedLag_eventual_separation d hd B hB
  refine ⟨M, fun n k hn hrep => ?_⟩
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (blockValue_nonneg 2 n k)
  obtain ⟨hnlo, hnhi⟩ := (BinaryDyadicOrbit.blockValue_eq_iff n k j).mp hj
  obtain ⟨hmlo, hmhi⟩ := (BinaryDyadicOrbit.blockValue_eq_iff (n + d) k j).mp (hrep.trans hj)
  let D := |BinaryDyadicOrbit.point (n + d) - BinaryDyadicOrbit.point n|
  have hscale : (0 : ℝ) < 2 ^ k := by positivity
  have hdist : D < 1 / (2 : ℝ) ^ k := by
    change |BinaryDyadicOrbit.point (n + d) - BinaryDyadicOrbit.point n| < 1 / (2 : ℝ) ^ k
    rw [show 1 / (2 : ℝ) ^ k =
        ((j : ℝ) + 1) / (2 : ℝ) ^ k - (j : ℝ) / (2 : ℝ) ^ k by ring, abs_lt]
    exact ⟨by linarith only [hnhi, hmlo], by linarith only [hmhi, hnlo]⟩
  have hsmall := pow_lt_pow_left₀ ((lt_div_iff₀ hscale).mp hdist)
    (mul_nonneg (abs_nonneg _) hscale.le) hB.ne'
  rw [mul_pow, ← pow_mul, one_pow, Nat.mul_comm k B] at hsmall
  by_contra! hn'
  have hlo : 1 ≤ D ^ B * (2 : ℝ) ^ n := by simpa only [Int.cast_zero, sub_zero] using hM n 0 hn
  exact (not_lt_of_ge (hlo.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by norm_num) hn') (pow_nonneg (abs_nonneg _) B)))) hsmall

/-- Ridout discharges the exact hypothesis used by the existing carry transfer. -/
theorem alpha_eventualDyadicSeparation :
    GoldenNormality.BinaryComplement.EventualDyadicSeparation := by
  have h := eventualDyadicSeparation_of_finite_candidates
    (ξ := GoldenNormality.alpha)
    GoldenNormality.BinaryDyadicOrbit.irrational_alpha
    GoldenNormality.alpha_pos GoldenNormality.alpha_lt_one
    (fun B hB => finite_dyadicCandidates algebraic_alpha hB)
  intro B hB
  obtain ⟨M, hM⟩ := h B hB
  exact ⟨M, fun m p hm => hM m hm p⟩

/-- Every coefficient below sqrt(2) eventually bounds the actual zero count below. -/
theorem zero_count_eventually_exceeds (c : ℝ) (hc : 0 ≤ c) (hcritical : c ^ 2 < 2) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.BinaryComplement.zero_count_eventually_exceeds_of_eventual_dyadic_separation
    alpha_eventualDyadicSeparation c hc hcritical

/-- Every coefficient below sqrt(8/pi) is exceeded at arbitrarily late prefixes. -/
theorem zero_count_exceeds (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 8) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.BinaryComplement.zero_count_exceeds_of_eventual_dyadic_separation
    alpha_eventualDyadicSeparation c hc hcritical M

end GoldenNormality.RidoutBridge
