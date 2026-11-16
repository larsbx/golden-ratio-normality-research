import GoldenNormality.BinaryThirdTailThreshold
import GoldenNormality.BinaryFixedFrequency

/-! Exact source transfer and a lag-two identity for the first scheduled frequency. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators

/-- The integer branch for tripling the fractional part of the complementary orbit. -/
noncomputable def thirdBranch (n : ℕ) : ℤ :=
  ⌊3 * Int.fract ((2 : ℝ) ^ n * BinaryComplement.beta)⌋

theorem thirdBranch_bounds (n : ℕ) : 0 ≤ thirdBranch n ∧ thirdBranch n < 3 := by
  unfold thirdBranch
  constructor
  · exact Int.floor_nonneg.mpr (mul_nonneg (by norm_num) (Int.fract_nonneg _))
  · apply Int.floor_lt.mpr
    norm_num
    linarith [Int.fract_lt_one ((2 : ℝ) ^ n * BinaryComplement.beta)]

theorem thirdSource_floor (n : ℕ) :
    ⌊(2 : ℝ) ^ n * thirdSource⌋ =
      3 * BinaryComplement.scaledFloor n - (2 : ℤ) ^ n + thirdBranch n := by
  let y := (2 : ℝ) ^ n * BinaryComplement.beta
  have hy : y = Int.fract y + (⌊y⌋ : ℝ) := (Int.fract_add_floor y).symm
  have he : (2 : ℝ) ^ n * thirdSource = 3 * Int.fract y +
      ((3 * ⌊y⌋ - (2 : ℤ) ^ n : ℤ) : ℝ) := by
    unfold thirdSource
    push_cast
    calc
      (2 : ℝ) ^ n * (3 * BinaryComplement.beta - 1) = 3 * y - (2 : ℝ) ^ n := by
        dsimp [y]
        ring
      _ = _ := by
        conv_lhs => rw [hy]
        ring
  rw [he, Int.floor_add_intCast]
  change thirdBranch n + (3 * BinaryComplement.scaledFloor n - (2 : ℤ) ^ n) = _
  ring

/-- A signed integer test for the branch, using the original carry residual. -/
theorem thirdBranch_ge_iff_residual (n : ℕ) (j : ℤ) (hj₂ : j ≤ 2) :
    j ≤ thirdBranch n ↔
      3 * (3 * (2 : ℤ) ^ n - 2 * BinaryComplement.scaledFloor n) * j - j ^ 2 ≤
        9 * BinaryComplement.prefixResidual n := by
  let B := (2 : ℝ) ^ n
  let q := (BinaryComplement.scaledFloor n : ℝ)
  let t := Int.fract (B * BinaryComplement.beta)
  let D := 3 * B - 2 * q
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hq : q ≤ B * BinaryComplement.beta := Int.floor_le _
  have ht : t < 1 := Int.fract_lt_one _
  have hb : BinaryComplement.beta < 1 / 2 := by
    by_contra! h
    nlinarith only [BinaryComplement.beta_quadratic, h,
      mul_pos BinaryComplement.beta_pos (sub_pos.mpr BinaryComplement.beta_lt_one)]
  have hDB : 2 * B ≤ D := by
    dsimp [D]
    nlinarith only [hq, mul_nonneg (sub_nonneg.mpr hb.le) (show 0 ≤ B from by linarith)]
  have hscale : B * BinaryComplement.beta = t + q := (Int.fract_add_floor _).symm
  have hP : (BinaryComplement.prefixResidual n : ℝ) = t * (D - t) := by
    have hr : (B * BinaryComplement.beta) ^ 2 - 3 * B * (B * BinaryComplement.beta) + B ^ 2 = 0 := by
      calc
        _ = B ^ 2 * (BinaryComplement.beta ^ 2 - 3 * BinaryComplement.beta + 1) := by ring
        _ = 0 := by rw [BinaryComplement.beta_quadratic, mul_zero]
    rw [hscale] at hr
    unfold BinaryComplement.prefixResidual BinaryComplement.quadraticResidual
    push_cast
    change q ^ 2 - 3 * B * q + B ^ 2 = _
    dsimp [D]
    nlinarith only [hr]
  have hj : (j : ℝ) ≤ 3 := by exact_mod_cast hj₂.trans (by norm_num : (2 : ℤ) ≤ 3)
  have hD : 2 ≤ D := by linarith
  have hc := rational_cutoff_iff_quadratic ht hD (by norm_num : (0 : ℝ) < 3) hj
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3), mul_comm t 3, ← hP,
    show (j : ℝ) * 3 * D = 3 * D * (j : ℝ) by ring, show (3 : ℝ) ^ 2 = 9 by norm_num] at hc
  change (j ≤ ⌊3 * t⌋) ↔ _
  rw [Int.le_floor, hc]
  dsimp only [D, B, q]
  constructor <;> intro h <;> exact_mod_cast h

/-- The polynomial residual at the transferred prefix is expressed in the signed
carry and its uncarried suffix from the original complementary source. -/
theorem thirdSource_residual_from_carry (n : ℕ) :
    let B := (2 : ℤ) ^ n
    let q := ⌊(2 : ℝ) ^ n * thirdSource⌋
    let j := thirdBranch n
    q ^ 2 - 7 * B * q + B ^ 2 =
      9 * (BinaryComplement.convolutionSuffix n - B * BinaryComplement.carry n) -
        3 * (3 * B - 2 * BinaryComplement.scaledFloor n) * j + j ^ 2 := by
  dsimp only
  rw [thirdSource_floor, show BinaryComplement.convolutionSuffix n -
      (2 : ℤ) ^ n * BinaryComplement.carry n = BinaryComplement.prefixResidual n by
    rw [BinaryComplement.carry_suffix_residual]; ring]
  unfold BinaryComplement.prefixResidual BinaryComplement.quadraticResidual
  ring

/-- Exact displacement from the reflected modular seed to the transformed
quadratic prefix. It costs at most three units of the final denominator. -/
theorem thirdSource_floor_add_branch_correction (n : ℕ) :
    ⌊(2 : ℝ) ^ n * thirdSource⌋ + (3 - thirdBranch n) =
      2 * (2 : ℤ) ^ n - 3 * scaledFloor 2 n := by
  rw [thirdSource_floor, BinaryComplement.scaledFloor_eq_complement]
  ring

private theorem lagTwo_phase (x : ℝ) (n : ℕ) :
    phaseAt x (n + 2) =
      Complex.exp ((((2 * Real.pi * (3 : ℝ) * ((2 : ℝ) ^ n * x) : ℝ) : ℂ) *
        Complex.I)) * phaseAt x n := by
  unfold phaseAt
  rw [← Complex.exp_add]
  congr 1
  rw [pow_add]
  push_cast
  ring

/-- Exact frequency-three real sum as the energy of the lag-two phase differences. -/
theorem real_averageAt_three_eq_lagTwo_energy (x : ℝ) (N : ℕ) (hN : 0 < N) :
    (averageAt x 3 N).re =
      1 - (∑ n ∈ Finset.range N, ‖phaseAt x (n + 2) - phaseAt x n‖ ^ 2) /
        (2 * (N : ℝ)) := by
  let w (n : ℕ) : ℂ := Complex.exp ((↑(2 * Real.pi * (3 : ℝ) * ((2 : ℝ) ^ n * x)) : ℂ) *
    Complex.I)
  have hterm (n : ℕ) :
      ‖phaseAt x (n + 2) - phaseAt x n‖ ^ 2 = 2 - 2 * (w n).re := by
    have hu : ‖phaseAt x n‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hw : ‖w n‖ = 1 := Complex.norm_exp_ofReal_mul_I _
    have hfactor : phaseAt x (n + 2) - phaseAt x n = (w n - 1) * phaseAt x n := by
      rw [lagTwo_phase]
      unfold w
      ring
    rw [hfactor, norm_mul, hu, mul_one, Complex.sq_norm, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hw] <;> ring
  unfold averageAt
  rw [Complex.div_natCast_re]
  norm_num only [Int.cast_ofNat]
  change (∑ n ∈ Finset.range N, w n).re / (N : ℝ) = _
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply]
  simp_rw [hterm]
  push_cast
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNR : (N : ℝ) ≠ 0 := by positivity
  field_simp [hNR] <;> ring

/-- The same exact identity for the repository's certified modular sum. -/
theorem real_dyadicModularAverage_three_eq_lagTwo_energy (N : ℕ) (hN : 0 < N) :
    let x := (scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N
    (dyadicModularAverage 3 N).re =
      1 - (∑ n ∈ Finset.range N, ‖phaseAt x (n + 2) - phaseAt x n‖ ^ 2) /
        (2 * (N : ℝ)) := by
  dsimp only
  rw [← show averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) 3 N =
    dyadicModularAverage 3 N from averageAt_dyadic _ _ _]
  exact real_averageAt_three_eq_lagTwo_energy _ N hN

/-- One-sided control of the scheduled mode is precisely a lower bound on
a mean squared lag-two difference. -/
theorem real_dyadicModularAverage_three_le_iff_lagTwo_energy
    (N : ℕ) (hN : 0 < N) (ε : ℝ) :
    let x := (scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N
    (dyadicModularAverage 3 N).re ≤ ε ↔
      2 * (N : ℝ) * (1 - ε) ≤
        ∑ n ∈ Finset.range N, ‖phaseAt x (n + 2) - phaseAt x n‖ ^ 2 := by
  dsimp only
  let E := ∑ n ∈ Finset.range N,
    ‖phaseAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) (n + 2) -
      phaseAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) n‖ ^ 2
  rw [real_dyadicModularAverage_three_eq_lagTwo_energy N hN]
  change (1 - E / (2 * (N : ℝ)) ≤ ε) ↔ 2 * (N : ℝ) * (1 - ε) ≤ E
  rw [mul_comm (2 * (N : ℝ)), ← le_div_iff₀ (by positivity : 0 < 2 * (N : ℝ))]
  constructor <;> intro h <;> linarith

end GoldenNormality.BinaryDyadicOrbit
