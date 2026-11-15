import RidoutBridge.FiniteToSeparation
import DiophantineApproximation.Ridout
import DiophantineApproximation.PrimeProducts

noncomputable section

open scoped BigOperators

namespace GoldenNormality.RidoutBridge

private theorem weighted_power_le_ridout_bound
    {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q)
    {B : ℕ} (hB : 0 < B)
    (h : x ^ B * q ^ (B + 1) ≤ 1) :
    x * q⁻¹ ≤ q ^ (-2 - (B : ℝ)⁻¹) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hexp : (-1 - (B : ℝ)⁻¹) * (B : ℝ) = -((B + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp [hBr.ne'] <;> ring
  have hpow :
      (q ^ (-1 - (B : ℝ)⁻¹)) ^ (B : ℝ) = 1 / q ^ (B + 1) := by
    calc
      (q ^ (-1 - (B : ℝ)⁻¹)) ^ (B : ℝ) =
          q ^ ((-1 - (B : ℝ)⁻¹) * (B : ℝ)) :=
        (Real.rpow_mul hq.le _ _).symm
      _ = q ^ (-((B + 1 : ℕ) : ℝ)) := by rw [hexp]
      _ = (q ^ ((B + 1 : ℕ) : ℝ))⁻¹ := Real.rpow_neg hq.le _
      _ = 1 / q ^ (B + 1) := by simp only [Real.rpow_natCast, one_div]
  have hroot : x ≤ q ^ (-1 - (B : ℝ)⁻¹) := by
    apply (Real.rpow_le_rpow_iff hx (Real.rpow_nonneg hq.le _) hBr).mp
    calc
      x ^ (B : ℝ) = x ^ B := Real.rpow_natCast _ _
      _ ≤ 1 / q ^ (B + 1) := (le_div_iff₀ (pow_pos hq _)).2 h
      _ = (q ^ (-1 - (B : ℝ)⁻¹)) ^ (B : ℝ) := hpow.symm
  calc
    x * q⁻¹ ≤ q ^ (-1 - (B : ℝ)⁻¹) * q⁻¹ :=
      mul_le_mul_of_nonneg_right hroot (inv_nonneg.mpr hq.le)
    _ = q ^ (-2 - (B : ℝ)⁻¹) := by
      rw [← Real.rpow_neg_one q, ← Real.rpow_add hq]
      congr 1
      ring

/-- Ridout with only the prime two gives a finite set of reduced dyadic
rationals satisfying the powered approximation bound. -/
theorem finite_dyadicCandidates
    {ξ : ℝ} (halg : IsAlgebraic ℚ ξ)
    {B : ℕ} (hB : 0 < B) :
    (DyadicCandidates ξ B).Finite := by
  classical
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hfin := Rat.finite_setOf_ridout halg ∅ (Nat.primesOf 2)
    (ε := (B : ℝ)⁻¹) (inv_pos.mpr hBr)
  refine hfin.subset ?_
  intro β hβ
  rcases hβ with ⟨hβ0, hβ1, ⟨m, hm⟩, hweight⟩
  have hqpos : (0 : ℝ) < β.den := by exact_mod_cast β.pos
  have hβ0r : (0 : ℝ) ≤ (β : ℝ) := by exact_mod_cast hβ0
  have hβ1r : (β : ℝ) ≤ 1 := by exact_mod_cast hβ1
  have hnumEq : (β.num : ℝ) = (β : ℝ) * (β.den : ℝ) := by
    rw [Rat.cast_def]
    exact (div_mul_cancel₀ _ hqpos.ne').symm
  have hnum0 : (0 : ℝ) ≤ β.num := by
    rw [hnumEq]
    exact mul_nonneg hβ0r hqpos.le
  have hnumle : (β.num : ℝ) ≤ β.den := by
    rw [hnumEq]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hβ1r hqpos.le
  have habsnumle : (β.num.natAbs : ℝ) ≤ β.den := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hnum0] using hnumle
  have hnumden : β.num.natAbs ≤ β.den := by exact_mod_cast habsnumle
  have hheight : (max β.num.natAbs β.den : ℝ) = (β.den : ℝ) := by
    exact_mod_cast (max_eq_right hnumden)
  have hpQ := Rat.prod_padicNorm_natCast (Nat.primesOf 2) β.den
    (Nat.ne_of_gt β.pos)
    (fun l hl => Nat.mem_primesOf_of_dvd_pow (n := 2) (k := m)
      (by decide) (hl.trans hm))
  have hprod :
      (∏ l ∈ Nat.primesOf 2,
        ((padicNorm (l : ℕ) (β.den : ℚ) : ℚ) : ℝ)) =
      (β.den : ℝ)⁻¹ := by
    have hh := congrArg (fun z : ℚ => (z : ℝ)) hpQ
    push_cast at hh
    exact hh
  simp only [Set.mem_setOf_eq, Finset.prod_empty, mul_one]
  rw [hprod, hheight]
  exact weighted_power_le_ridout_bound (abs_nonneg _) hqpos hB hweight

end GoldenNormality.RidoutBridge
