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
