import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic

namespace GoldenNormality.RidoutBridge

/-- Reduced dyadic rationals in the unit interval with a strong approximation bound. -/
def DyadicCandidates (ξ : ℝ) (B : ℕ) : Set ℚ :=
  {β : ℚ | 0 ≤ β ∧ β ≤ 1 ∧ (∃ m : ℕ, β.den ∣ 2 ^ m) ∧
    |ξ - (β : ℝ)| ^ B * (β.den : ℝ) ^ (B + 1) ≤ 1}

private theorem infinite_of_arbitrarily_close {ξ : ℝ} (hirr : Irrational ξ)
    {X : Set ℚ}
    (h : ∀ η : ℝ, 0 < η → ∃ β ∈ X, |ξ - (β : ℝ)| < η) : X.Infinite := by
  intro hfin
  obtain ⟨β₀, hβ₀, -⟩ := h 1 one_pos
  obtain ⟨b, hbX, hb⟩ :=
    Set.exists_min_image X (fun β ↦ |ξ - (β : ℝ)|) hfin ⟨β₀, hβ₀⟩
  have hbpos : 0 < |ξ - (b : ℝ)| :=
    abs_pos.mpr (sub_ne_zero.mpr fun heq ↦ hirr ⟨b, heq.symm⟩)
  obtain ⟨c, hcX, hc⟩ := h _ hbpos
  exact absurd (hb c hcX) (not_le.mpr hc)

/-- Finiteness of reduced dyadic exceptional rationals gives eventual separation
for every integer numerator, including unreduced dyadics. -/
theorem eventualDyadicSeparation_of_finite_candidates {ξ : ℝ}
    (hirr : Irrational ξ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hfinite : ∀ B : ℕ, 0 < B → (DyadicCandidates ξ B).Finite) :
    ∀ B : ℕ, 0 < B → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ p : ℤ,
      1 ≤ |(2 : ℝ) ^ m * ξ - (p : ℝ)| ^ B * (2 : ℝ) ^ m := by
  classical
  intro B hB
  by_contra hfail
  push_neg at hfail
  have hinf : (DyadicCandidates ξ B).Infinite := by
    refine infinite_of_arbitrarily_close hirr ?_
    intro η hη
    let r : ℝ := min η (min ξ (1 - ξ))
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min hη (lt_min hξ0 (sub_pos.mpr hξ1))
    have hrη : r ≤ η := min_le_left _ _
    have hrξ : r ≤ ξ := (min_le_right _ _).trans (min_le_left _ _)
    have hr1 : r ≤ 1 - ξ := (min_le_right _ _).trans (min_le_right _ _)
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt r⁻¹ (by norm_num : (1 : ℝ) < 2)
    obtain ⟨m, hm, p, hp⟩ := hfail N
    let q : ℕ := 2 ^ m
    let β : ℚ := (p : ℚ) / (q : ℚ)
    have hqposN : 0 < q := by dsimp [q]; positivity
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposN
    have hqcast : (q : ℝ) = (2 : ℝ) ^ m := by simp [q]
    have hqone : (1 : ℝ) ≤ q := by
      rw [hqcast]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hqbig : r⁻¹ < (q : ℝ) := by
      rw [hqcast]
      exact hN.trans_le (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm)
    have hqinv : (q : ℝ)⁻¹ < r := (inv_lt_comm₀ hr hqpos).mp hqbig
    have hp' : |(q : ℝ) * ξ - (p : ℝ)| ^ B * (q : ℝ) < 1 := by
      simpa only [hqcast] using hp
    have hscaledpow : |(q : ℝ) * ξ - (p : ℝ)| ^ B ≤ 1 :=
      (le_mul_of_one_le_right (pow_nonneg (abs_nonneg _) B) hqone).trans hp'.le
    have hscaledle : |(q : ℝ) * ξ - (p : ℝ)| ≤ 1 :=
      (pow_le_one_iff_of_nonneg (abs_nonneg _) hB.ne').mp hscaledpow
    have hβcast : (β : ℝ) = (p : ℝ) / (q : ℝ) := by
      dsimp [β]
      push_cast <;> rfl
    have hscale : |ξ - (β : ℝ)| * (q : ℝ) = |(q : ℝ) * ξ - (p : ℝ)| := by
      calc
        |ξ - (β : ℝ)| * (q : ℝ) = |(ξ - (β : ℝ)) * (q : ℝ)| := by
          rw [abs_mul, abs_of_pos hqpos]
        _ = |(q : ℝ) * ξ - (p : ℝ)| := by
          congr 1
          rw [hβcast]
          field_simp [ne_of_gt hqpos] <;> ring
    have hdist : |ξ - (β : ℝ)| ≤ (q : ℝ)⁻¹ := by
      rw [← one_div, le_div_iff₀ hqpos, hscale]
      exact hscaledle
    have hsmall : |ξ - (β : ℝ)| < r := hdist.trans_lt hqinv
    have hβ0R : (0 : ℝ) ≤ (β : ℝ) := by
      have hu := (abs_lt.mp (hsmall.trans_le hrξ)).2
      linarith
    have hβ1R : (β : ℝ) ≤ 1 := by
      have hl := (abs_lt.mp (hsmall.trans_le hr1)).1
      linarith
    have hden : β.den ∣ q := by
      have hd := Rat.den_dvd p (q : ℤ)
      have hβdiv : β = Rat.divInt p (q : ℤ) := by
        rw [Rat.divInt_eq_div]
        push_cast <;> rfl
      rw [hβdiv]
      exact_mod_cast hd
    have hdenle : (β.den : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hqposN hden
    have hraw : |ξ - (β : ℝ)| ^ B * (q : ℝ) ^ (B + 1) < 1 := by
      calc
        |ξ - (β : ℝ)| ^ B * (q : ℝ) ^ (B + 1)
            = (|ξ - (β : ℝ)| * (q : ℝ)) ^ B * (q : ℝ) := by
              rw [mul_pow, pow_succ]
              ring
        _ = |(q : ℝ) * ξ - (p : ℝ)| ^ B * (q : ℝ) := by rw [hscale]
        _ < 1 := hp'
    refine ⟨β, ?_, hsmall.trans_le hrη⟩
    change 0 ≤ β ∧ β ≤ 1 ∧ (∃ j : ℕ, β.den ∣ 2 ^ j) ∧
      |ξ - (β : ℝ)| ^ B * (β.den : ℝ) ^ (B + 1) ≤ 1
    refine ⟨by exact_mod_cast hβ0R, by exact_mod_cast hβ1R, ⟨m, hden⟩, ?_⟩
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hdenle (B + 1))
      (pow_nonneg (abs_nonneg _) B)).trans hraw.le
  exact hinf (hfinite B hB)

end GoldenNormality.RidoutBridge
