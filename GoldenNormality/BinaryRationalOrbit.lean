import GoldenNormality.BinaryWeylCriterion
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantitative transfer from certified rational approximants to actual orbit averages. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Topology
open Filter

/-- Use the same first (N) starts for an arbitrary real source. -/
noncomputable def averageAt (x : ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, Complex.exp
    ((((2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * x)) : ℝ) : ℂ) * Complex.I)) / (N : ℂ)

theorem average_eq_averageAt (h : ℤ) (N : ℕ) :
    average h N = averageAt alpha h N := rfl

private theorem exp_phase_distance (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I)‖ ≤ |a - b| := by
  have harg : (((a - b : ℝ) : ℂ) * Complex.I) + (b : ℂ) * Complex.I =
      (a : ℂ) * Complex.I := by push_cast; ring
  have he : Complex.exp ((a : ℂ) * Complex.I) - Complex.exp ((b : ℂ) * Complex.I) =
      (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) *
        Complex.exp ((b : ℂ) * Complex.I) := by
    rw [sub_mul, one_mul, ← Complex.exp_add, harg]
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  simpa only [mul_comm Complex.I, Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := a - b))

theorem norm_averageAt_sub_le (x y : ℝ) (h : ℤ) (N : ℕ) :
    ‖averageAt x h N - averageAt y h N‖ ≤
      (2 * Real.pi * |(h : ℝ)| * ((2 : ℝ) ^ N - 1) * |x - y|) / (N : ℝ) := by
  unfold averageAt
  rw [← sub_div, norm_div, Complex.norm_natCast, ← Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ n ∈ Finset.range N,
      ‖Complex.exp ((((2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * x)) : ℝ) : ℂ) * Complex.I) -
        Complex.exp ((((2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * y)) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, 2 * Real.pi * |(h : ℝ)| * |x - y| * (2 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro n _
      refine (exp_phase_distance _ _).trans_eq ?_
      rw [show 2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * x) -
        2 * Real.pi * h * ((2 : ℝ) ^ n * y) =
          (2 * Real.pi) * (h : ℝ) * (x - y) * (2 : ℝ) ^ n by ring]
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi),
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]
    _ = _ := by
      rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
      ring

/-- Binary truncation after (N) digits preserves every fixed mode up to
a uniform (2pi |h|/N) error in the normalized average. -/
theorem norm_average_sub_dyadic_prefix_le (h : ℤ) (N : ℕ) :
    ‖average h N - averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N‖ ≤
      2 * Real.pi * |(h : ℝ)| / (N : ℝ) := by
  let B := (2 : ℝ) ^ N
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num)
  let p := (scaledFloor 2 N : ℝ)
  have hfloor := Int.floor_le (B * alpha)
  have hceil := Int.lt_floor_add_one (B * alpha)
  change p ≤ B * alpha at hfloor
  change B * alpha < p + 1 at hceil
  have hx : 0 ≤ alpha - p / B := by
    apply sub_nonneg.mpr
    rw [div_le_iff₀ hB, mul_comm]
    exact hfloor
  have he : B * |alpha - p / B| < 1 := by
    rw [abs_of_nonneg hx, mul_sub, mul_div_cancel₀ _ hB.ne']
    linarith only [hceil]
  rw [average_eq_averageAt]
  refine (norm_averageAt_sub_le alpha (p / B) h N).trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hBsub : B - 1 ≤ B := sub_le_self _ zero_le_one
  have hb := mul_le_mul_of_nonneg_right hBsub (abs_nonneg (alpha - p / B))
  have hcoef : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  change 2 * Real.pi * |(h : ℝ)| * (B - 1) * |alpha - p / B| ≤ _
  rw [mul_assoc]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hb.trans he.le) hcoef

/-- Checking the approximating finite sums can use exact dyadic modular residues. -/
theorem averageAt_dyadic (p : ℤ) (h : ℤ) (N : ℕ) :
    averageAt ((p : ℝ) / (2 : ℝ) ^ N) h N =
      (∑ n ∈ Finset.range N, ZMod.stdAddChar
        ((h : ZMod (2 ^ N)) * (p : ZMod (2 ^ N)) * (2 : ZMod (2 ^ N)) ^ n)) / (N : ℂ) := by
  have : NeZero (2 ^ N : ℕ) := ⟨by positivity⟩
  unfold averageAt
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have he : (h : ZMod (2 ^ N)) * (p : ZMod (2 ^ N)) * (2 : ZMod (2 ^ N)) ^ n =
      ((h * p * (2 : ℤ) ^ n : ℤ) : ZMod (2 ^ N)) := by push_cast; rfl
  rw [he, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

/-- The certified dyadic-prefix averages are an equivalent odd-mode obligation. -/
theorem tendsto_average_dyadic_prefix_iff (h : ℤ) :
    Tendsto (average h) atTop (𝓝 0) ↔
      Tendsto (fun N => averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N) atTop (𝓝 0) := by
  let f := fun N => averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N
  have hd : Tendsto (fun N => average h N - f N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi * |(h : ℝ)|))
      (fun _ => norm_nonneg _) (norm_average_sub_dyadic_prefix_le h)
  constructor
  · intro ha
    have he : (fun N => average h N - (average h N - f N)) = f := by
      funext N
      ring
    have ht := ha.sub hd
    rwa [he, sub_zero] at ht
  · intro hf
    have he : (fun N => average h N - f N + f N) = average h := by
      funext N
      ring
    have ht := hd.add hf
    rwa [he, add_zero] at ht

/-- The exact finite sum using the certified dyadic floor and its residues. -/
noncomputable def dyadicModularAverage (h : ℤ) (N : ℕ) : ℂ :=
  have : NeZero (2 ^ N : ℕ) := ⟨by positivity⟩
  (∑ n ∈ Finset.range N, ZMod.stdAddChar
    ((h : ZMod (2 ^ N)) * (scaledFloor 2 N : ZMod (2 ^ N)) *
      (2 : ZMod (2 ^ N)) ^ n)) / (N : ℂ)

theorem tendsto_average_iff_dyadic_modular (h : ℤ) :
    Tendsto (average h) atTop (𝓝 0) ↔ Tendsto (dyadicModularAverage h) atTop (𝓝 0) := by
  rw [tendsto_average_dyadic_prefix_iff]
  have he : (fun N => averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N) =
      dyadicModularAverage h := by
    funext N
    exact averageAt_dyadic (scaledFloor 2 N) h N
  rw [he]

/-- Cancellation can be sought in exact finite sums of cyclotomic phases
whose residues use the source-bound quadratic floor. -/
theorem normalInBase_of_dyadic_modular_cancellation
    (hc : ∀ h : ℤ, h % 2 = 1 → Tendsto (dyadicModularAverage h) atTop (𝓝 0)) :
    NormalInBase 2 := by
  apply normalInBase_of_odd_mode_cancellation
  intro h ho
  exact (tendsto_average_iff_dyadic_modular h).mpr (hc h ho)

end GoldenNormality.BinaryDyadicOrbit
