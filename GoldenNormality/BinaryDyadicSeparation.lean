import GoldenNormality.BinaryDyadicOrbit
import Mathlib.NumberTheory.Real.Irrational

/-! Exact quadratic-norm bounds for close returns of the actual binary orbit. -/

namespace GoldenNormality.BinaryDyadicOrbit

theorem irrational_alpha : Irrational alpha := by
  have h5 : Irrational (Real.sqrt 5) := by
    exact_mod_cast (show Nat.Prime 5 by decide).irrational_sqrt
  unfold alpha
  convert (h5.sub_intCast 1).div_ratCast (q := 2) (by decide) using 2 <;> norm_num

private theorem quadratic_norm_identity (q p : ℤ) :
    ((q : ℝ) * alpha - p) * ((q : ℝ) * alpha - p - Real.sqrt 5 * q) =
      ((p ^ 2 + p * q - q ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt 5 = 2 * alpha + 1 := by unfold alpha; ring
  push_cast
  rw [hs]
  linear_combination -(q : ℝ) ^ 2 * alpha_quadratic

/-- The product of both real conjugates has nonzero integer magnitude. -/
theorem quadratic_norm_abs_ge_one (q p : ℤ) (hq : q ≠ 0) :
    1 ≤ |(q : ℝ) * alpha - p| * |(q : ℝ) * alpha - p - Real.sqrt 5 * q| := by
  have hirr := irrational_alpha.intCast_mul hq
  have hleft := hirr.ne_int p
  have he : (q : ℝ) * alpha - p - Real.sqrt 5 * q = -((q : ℝ) * alpha + (p + q : ℤ)) := by
    have hs : Real.sqrt 5 = 2 * alpha + 1 := by unfold alpha; ring
    push_cast
    rw [hs]
    ring
  have hright : (q : ℝ) * alpha - p - Real.sqrt 5 * q ≠ 0 := by
    rw [he, neg_ne_zero]
    intro h
    apply hirr.ne_int (-(p + q))
    push_cast at h ⊢
    linarith only [h]
  have hpq : p ^ 2 + p * q - q ^ 2 ≠ 0 := by
    intro hz
    have hprod := mul_ne_zero (sub_ne_zero.mpr hleft) hright
    rw [quadratic_norm_identity, hz, Int.cast_zero] at hprod
    exact hprod rfl
  rw [← abs_mul, quadratic_norm_identity]
  exact_mod_cast (show (1 : ℤ) ≤ |p ^ 2 + p * q - q ^ 2| by
    exact Int.add_one_le_iff.mpr (abs_pos.mpr hpq))

theorem rational_separation (q p : ℤ) (hq : q ≠ 0) :
    1 ≤ |(q : ℝ) * alpha - p| *
      (|(q : ℝ) * alpha - p| + Real.sqrt 5 * |(q : ℝ)|) := by
  refine (quadratic_norm_abs_ge_one q p hq).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
  simpa only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
    abs_sub_le ((q : ℝ) * alpha - p) 0 (Real.sqrt 5 * q)

theorem return_separation (m n : ℕ) (hnm : n < m) :
    1 ≤ |point m - point n| *
      (|point m - point n| + Real.sqrt 5 * ((2 : ℝ) ^ m - (2 : ℝ) ^ n)) := by
  let q : ℤ := 2 ^ m - 2 ^ n
  let p : ℤ := scaledFloor 2 m - scaledFloor 2 n
  have hqcast : (q : ℝ) = (2 : ℝ) ^ m - (2 : ℝ) ^ n := by simp [q]
  have hqpos : 0 < (q : ℝ) := by
    rw [hqcast]
    exact sub_pos.mpr (pow_lt_pow_right₀ (by norm_num) hnm)
  have hq : q ≠ 0 := by exact_mod_cast hqpos.ne'
  have hd : (q : ℝ) * alpha - p = point m - point n := by
    rw [hqcast]
    simp only [point, p, scaledFloor, Nat.cast_ofNat, Int.cast_sub, Int.fract]
    ring
  have hb := rational_separation q p hq
  rwa [hd, abs_of_pos hqpos, hqcast] at hb

/-- Repeated actual blocks must obey a strict bound on their shared width. -/
theorem repeated_block_width_lt (m n k : ℕ) (hnm : n < m)
    (h : blockValue 2 m k = blockValue 2 n k) :
    (2 : ℝ) ^ k < 1 + Real.sqrt 5 * ((2 : ℝ) ^ m - (2 : ℝ) ^ n) := by
  have hv : 0 ≤ blockValue 2 n k := blockValue_nonneg 2 n k
  obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le hv
  obtain ⟨hnlo, hnhi⟩ := (blockValue_eq_iff n k j).mp hj
  obtain ⟨hmlo, hmhi⟩ := (blockValue_eq_iff m k j).mp (h.trans hj)
  let B : ℝ := (2 : ℝ) ^ k
  have hB : 0 < B := by dsimp [B]; positivity
  have hB1 : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hwidth : ((j : ℝ) + 1) / B - (j : ℝ) / B = 1 / B := by
    rw [← sub_div, add_sub_cancel_left]
  have hdist : |point m - point n| < 1 / B := by
    rw [← hwidth, abs_lt]
    exact ⟨by linarith only [hnhi, hmlo], by linarith only [hmhi, hnlo]⟩
  let A := Real.sqrt 5 * ((2 : ℝ) ^ m - (2 : ℝ) ^ n)
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _)
    (sub_nonneg.mpr (pow_lt_pow_right₀ (by norm_num) hnm).le)
  have hd1 : |point m - point n| ≤ 1 :=
    hdist.le.trans (div_le_one_of_le₀ hB1 hB.le)
  have hmul : 1 ≤ |point m - point n| * (1 + A) :=
    (return_separation m n hnm).trans
      (mul_le_mul_of_nonneg_left (add_le_add_left hd1 A) (abs_nonneg _))
  have hlt := mul_lt_mul_of_pos_right hdist (show 0 < 1 + A by linarith only [hA])
  rw [div_mul_eq_mul_div, one_mul] at hlt
  have hb := (lt_div_iff₀ hB).mp (hmul.trans_lt hlt)
  simpa only [one_mul] using hb

/-- Any repeated block at distinct starts has width at most the later start plus one. -/
theorem repeated_block_width_le (m n k : ℕ) (hnm : n < m)
    (h : blockValue 2 m k = blockValue 2 n k) : k ≤ m + 1 := by
  by_contra! hk
  have hp : (2 : ℝ) ^ (m + 2) ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hs : Real.sqrt 5 < 3 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
  have hm : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have hprod : Real.sqrt 5 * ((2 : ℝ) ^ m - (2 : ℝ) ^ n) < 3 * (2 : ℝ) ^ m := by
    calc
      _ ≤ Real.sqrt 5 * (2 : ℝ) ^ m := by
        exact mul_le_mul_of_nonneg_left (sub_le_self _ hn.le) (Real.sqrt_nonneg _)
      _ < _ := mul_lt_mul_of_pos_right hs (by positivity)
  rw [pow_add] at hp
  norm_num at hp
  linarith only [hp, hm, hprod, repeated_block_width_lt m n k hnm h]

private theorem floor_of_prefix_certificate (n q : ℕ) (h : PrefixCertificate (2 ^ n) q) :
    scaledFloor 2 n = (q : ℤ) := by
  simpa only [scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using
    (prefixCertificate_iff_intFloor (by positivity : 0 < (2 : ℕ) ^ n)).mp h

/-- The nonconstant block 110111 recurs with overlap at starts 10 and 14. -/
theorem actual_overlapping_repeat :
    blockValue 2 10 6 = 55 ∧ blockValue 2 14 6 = 55 := by
  have h10 := floor_of_prefix_certificate 10 632 (by decide)
  have h14 := floor_of_prefix_certificate 14 10125 (by decide)
  have h16 := floor_of_prefix_certificate 16 40503 (by decide)
  have h20 := floor_of_prefix_certificate 20 648055 (by decide)
  constructor
  · change scaledFloor 2 16 - (2 : ℤ) ^ 6 * scaledFloor 2 10 = _
    rw [h16, h10]
    norm_num
  · change scaledFloor 2 20 - (2 : ℤ) ^ 6 * scaledFloor 2 14 = _
    rw [h20, h14]
    norm_num

end GoldenNormality.BinaryDyadicOrbit
