import GoldenNormality.BinaryComplementCarry

/-! Rational cutoff decisions for the frequency-three source. -/

namespace GoldenNormality.BinaryDyadicOrbit

/-- The complementary source of the scheduled frequency three. -/
noncomputable def thirdSource : ℝ := 3 * BinaryComplement.beta - 1

theorem thirdSource_eq_two_sub : thirdSource = 2 - 3 * alpha := by
  unfold thirdSource BinaryComplement.beta
  ring

theorem thirdSource_quadratic : thirdSource ^ 2 - 7 * thirdSource + 1 = 0 := by
  unfold thirdSource
  nlinarith only [BinaryComplement.beta_quadratic]

/-- A quadratic residual determines a rational tail comparison on a monotone branch. -/
theorem rational_cutoff_iff_quadratic
    {t D a m : ℝ} (ht : t < 1) (hD : 2 ≤ D)
    (hm : 0 < m) (ha : a ≤ m) :
    a / m ≤ t ↔ a * m * D - a ^ 2 ≤ m ^ 2 * (t * (D - t)) := by
  have hmargin : 0 < m * (D - t - 1) := mul_pos hm (by linarith)
  have hfactor : 0 < m * D - m * t - a := by nlinarith only [hmargin, ha]
  have hdiff : m ^ 2 * (t * (D - t)) - (a * m * D - a ^ 2) =
      (t * m - a) * (m * D - m * t - a) := by ring
  calc
    a / m ≤ t ↔ a ≤ t * m := div_le_iff₀ hm
    _ ↔ 0 ≤ t * m - a := sub_nonneg.symm
    _ ↔ 0 ≤ (t * m - a) * (m * D - m * t - a) :=
      (mul_nonneg_iff_of_pos_right hfactor).symm
    _ ↔ a * m * D - a ^ 2 ≤ m ^ 2 * (t * (D - t)) := by
      rw [← hdiff, sub_nonneg]

/-- The exact force of the cutoff test, retaining the integer denominator and prefix. -/
theorem thirdTail_rational_cutoff (n : ℕ) (a m : ℤ) (hm : 0 < m) (ha : a ≤ m) :
    let B := (2 : ℤ) ^ n
    let r := ⌊(2 : ℝ) ^ n * thirdSource⌋
    let R := r ^ 2 - 7 * B * r + B ^ 2
    (a : ℝ) / (m : ℝ) ≤ Int.fract ((2 : ℝ) ^ n * thirdSource) ↔
      a * m * (7 * B - 2 * r) - a ^ 2 ≤ m ^ 2 * R := by
  dsimp only
  let B := (2 : ℝ) ^ n
  let r := (⌊B * thirdSource⌋ : ℝ)
  let t := Int.fract (B * thirdSource)
  let D := 7 * B - 2 * r
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hthird : thirdSource < 1 := by
    unfold thirdSource
    nlinarith only [BinaryComplement.beta_quadratic,
      mul_pos BinaryComplement.beta_pos (sub_pos.mpr BinaryComplement.beta_lt_one)]
  have hr : r ≤ B := by
    exact (Int.floor_le (B * thirdSource)).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hthird.le (by linarith))
  have hD : 2 ≤ D := by dsimp [D]; linarith
  have ht : t < 1 := Int.fract_lt_one _
  have hy : B * thirdSource = t + r := (Int.fract_add_floor _).symm
  have hR : r ^ 2 - 7 * B * r + B ^ 2 = t * (D - t) := by
    have hroot : (B * thirdSource) ^ 2 - 7 * B * (B * thirdSource) + B ^ 2 = 0 := by
      calc
        _ = B ^ 2 * (thirdSource ^ 2 - 7 * thirdSource + 1) := by ring
        _ = 0 := by rw [thirdSource_quadratic, mul_zero]
    rw [hy] at hroot
    dsimp [D]
    nlinarith only [hroot]
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have ha' : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ha
  rw [show Int.fract ((2 : ℝ) ^ n * thirdSource) = t by rfl,
    rational_cutoff_iff_quadratic ht hD hm' ha', ← hR]
  dsimp only [D, B, r]
  constructor <;> intro h <;> exact_mod_cast h

end GoldenNormality.BinaryDyadicOrbit
