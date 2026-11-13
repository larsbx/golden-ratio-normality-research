import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact certificates for finite prefixes of the golden ratio

The certificate uses only natural-number inequalities.  Its soundness theorem
connects those inequalities to the positive real root of `x^2 + x = 1`.
All statements are universal; finite examples are separate consumers.
-/

namespace GoldenNormality

noncomputable def alpha : ℝ := (Real.sqrt 5 - 1) / 2

/-- The explicit fractional part of `(1 + sqrt 5) / 2`. -/
theorem alpha_eq_goldenRatio_sub_one : alpha = (1 + Real.sqrt 5) / 2 - 1 := by
  unfold alpha
  ring

theorem alpha_pos : 0 < alpha := by
  unfold alpha
  nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem alpha_lt_one : alpha < 1 := by
  unfold alpha
  nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem alpha_quadratic : alpha ^ 2 + alpha = 1 := by
  unfold alpha
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

/-- The candidate `q` lies immediately below the positive root at scale `B`. -/
def PrefixCertificate (B q : ℕ) : Prop :=
  q ^ 2 + B * q ≤ B ^ 2 ∧ B ^ 2 < (q + 1) ^ 2 + B * (q + 1)

instance (B q : ℕ) : Decidable (PrefixCertificate B q) :=
  inferInstanceAs (Decidable
    (q ^ 2 + B * q ≤ B ^ 2 ∧ B ^ 2 < (q + 1) ^ 2 + B * (q + 1)))

/-- Executable checking includes the strictly positive scale. -/
def checkPrefix (B q : ℕ) : Bool := decide (0 < B ∧ PrefixCertificate B q)

theorem checkPrefix_iff (B q : ℕ) :
    checkPrefix B q = true ↔ 0 < B ∧ PrefixCertificate B q := by
  simp [checkPrefix]

private theorem quadratic_strictMono {B u v : ℝ} (hB : 0 < B)
    (hu : 0 ≤ u) (huv : u < v) : u ^ 2 + B * u < v ^ 2 + B * v := by
  have hd : 0 < v - u := sub_pos.mpr huv
  have hp := mul_pos hB hd
  have hq := mul_nonneg hu (le_of_lt hd)
  nlinarith [sq_nonneg (v - u)]

theorem prefixCertificate_iff_bounds {B q : ℕ} (hB : 0 < B) :
    PrefixCertificate B q ↔
      (q : ℝ) ≤ (B : ℝ) * alpha ∧ (B : ℝ) * alpha < (q : ℝ) + 1 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hy : 0 ≤ (B : ℝ) * alpha := mul_nonneg (le_of_lt hBr) (le_of_lt alpha_pos)
  have hroot : ((B : ℝ) * alpha) ^ 2 + (B : ℝ) * ((B : ℝ) * alpha) =
      (B : ℝ) ^ 2 := by
    calc
      _ = (B : ℝ) ^ 2 * (alpha ^ 2 + alpha) := by ring
      _ = (B : ℝ) ^ 2 := by rw [alpha_quadratic]; ring
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  constructor
  · rintro ⟨hl, hr⟩
    have hlr : (q : ℝ) ^ 2 + (B : ℝ) * q ≤ (B : ℝ) ^ 2 := by
      exact_mod_cast hl
    have hrr : (B : ℝ) ^ 2 < ((q : ℝ) + 1) ^ 2 + (B : ℝ) * ((q : ℝ) + 1) := by
      exact_mod_cast hr
    constructor
    · by_contra hn
      have hh := quadratic_strictMono hBr hy (lt_of_not_ge hn)
      linarith
    · by_contra hn
      have he : (q : ℝ) + 1 ≤ (B : ℝ) * alpha := le_of_not_gt hn
      rcases eq_or_lt_of_le he with hh | hh
      · rw [← hh] at hroot
        linarith
      · have hm := quadratic_strictMono hBr (by positivity : (0 : ℝ) ≤ (q : ℝ) + 1) hh
        linarith
  · rintro ⟨hl, hr⟩
    have hlr : (q : ℝ) ^ 2 + (B : ℝ) * q ≤ (B : ℝ) ^ 2 := by
      rcases eq_or_lt_of_le hl with hh | hh
      · rw [hh]
        exact le_of_eq hroot
      · have hm := quadratic_strictMono hBr hq hh
        linarith
    have hrr : (B : ℝ) ^ 2 < ((q : ℝ) + 1) ^ 2 + (B : ℝ) * ((q : ℝ) + 1) := by
      have hm := quadratic_strictMono hBr hy hr
      linarith
    exact ⟨by exact_mod_cast hlr, by exact_mod_cast hrr⟩

theorem prefixCertificate_iff_natFloor {B q : ℕ} (hB : 0 < B) :
    PrefixCertificate B q ↔ Nat.floor ((B : ℝ) * alpha) = q := by
  rw [Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg B) (le_of_lt alpha_pos))]
  exact prefixCertificate_iff_bounds hB

theorem prefixCertificate_iff_intFloor {B q : ℕ} (hB : 0 < B) :
    PrefixCertificate B q ↔ Int.floor ((B : ℝ) * alpha) = (q : ℤ) := by
  rw [Int.floor_eq_iff]
  simpa only [Int.cast_natCast] using prefixCertificate_iff_bounds (q := q) hB

theorem checkPrefix_sound {B q : ℕ} (h : checkPrefix B q = true) :
    Nat.floor ((B : ℝ) * alpha) = q := by
  obtain ⟨hB, hc⟩ := (checkPrefix_iff B q).mp h
  exact (prefixCertificate_iff_natFloor hB).mp hc

theorem prefixCertificate_unique {B q r : ℕ} (hB : 0 < B)
    (hq : PrefixCertificate B q) (hr : PrefixCertificate B r) : q = r := by
  exact ((prefixCertificate_iff_natFloor hB).mp hq).symm.trans
    ((prefixCertificate_iff_natFloor hB).mp hr)

theorem certified_prefix_lt_scale {B q : ℕ} (hB : 0 < B)
    (h : PrefixCertificate B q) : q < B := by
  have hl := ((prefixCertificate_iff_bounds hB).mp h).1
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hu := mul_lt_mul_of_pos_left alpha_lt_one hBr
  have hh : (q : ℝ) < B := by linarith
  exact_mod_cast hh

/-- Signed residual, so an invalid candidate never truncates a negative value. -/
def residual (B q : ℤ) : ℤ := B ^ 2 - q ^ 2 - B * q

theorem residual_step (b B q d : ℤ) :
    residual (b * B) (b * q + d) =
      b ^ 2 * residual B q - b * d * (2 * q + B) - d ^ 2 := by
  unfold residual
  ring

theorem prefixCertificate_iff_residual (B q : ℕ) :
    PrefixCertificate B q ↔
      0 ≤ residual B q ∧ residual B q < 2 * (q : ℤ) + B + 1 := by
  unfold PrefixCertificate residual
  constructor
  · rintro ⟨hl, hr⟩
    have hl' : (q : ℤ) ^ 2 + (B : ℤ) * q ≤ (B : ℤ) ^ 2 := by exact_mod_cast hl
    have hr' : (B : ℤ) ^ 2 < ((q : ℤ) + 1) ^ 2 + (B : ℤ) * ((q : ℤ) + 1) := by
      exact_mod_cast hr
    constructor <;> nlinarith
  · rintro ⟨hl, hr⟩
    have hl' : (q : ℤ) ^ 2 + (B : ℤ) * q ≤ (B : ℤ) ^ 2 := by linarith
    have hr' : (B : ℤ) ^ 2 < ((q : ℤ) + 1) ^ 2 + (B : ℤ) * ((q : ℤ) + 1) := by
      nlinarith
    exact ⟨by exact_mod_cast hl', by exact_mod_cast hr'⟩

noncomputable def scaledFloor (b n : ℕ) : ℤ := Int.floor ((b : ℝ) ^ n * alpha)

/-- The integer value of a length-`k` contiguous block beginning at zero-indexed `n`. -/
noncomputable def blockValue (b n k : ℕ) : ℤ :=
  scaledFloor b (n + k) - (b : ℤ) ^ k * scaledFloor b n

noncomputable def digit (b n : ℕ) : ℤ := blockValue b n 1

/-- Two independently checked adjacent prefixes determine the actual digit. -/
theorem digit_of_certificates {b n q r : ℕ} (hb : 2 ≤ b)
    (hq : PrefixCertificate (b ^ n) q)
    (hr : PrefixCertificate (b ^ (n + 1)) r) :
    digit b n = (r : ℤ) - (b : ℤ) * q := by
  have hbpos : 0 < b := lt_of_lt_of_le (by decide : 0 < 2) hb
  have hq' : scaledFloor b n = (q : ℤ) := by
    simpa only [scaledFloor, Nat.cast_pow] using
      (prefixCertificate_iff_intFloor (pow_pos hbpos n)).mp hq
  have hr' : scaledFloor b (n + 1) = (r : ℤ) := by
    simpa only [scaledFloor, Nat.cast_pow] using
      (prefixCertificate_iff_intFloor (pow_pos hbpos (n + 1))).mp hr
  simp only [digit, blockValue, pow_one, hq', hr']

theorem blockValue_eq_floor_fract (b n k : ℕ) :
    blockValue b n k = Int.floor ((b : ℝ) ^ k * Int.fract ((b : ℝ) ^ n * alpha)) := by
  unfold blockValue scaledFloor
  rw [Int.fract, mul_sub]
  have he : (b : ℝ) ^ k * ((b : ℝ) ^ n * alpha) = (b : ℝ) ^ (n + k) * alpha := by
    rw [pow_add]
    ring
  rw [he]
  have hc : (b : ℝ) ^ k * (Int.floor ((b : ℝ) ^ n * alpha) : ℝ) =
      (((b : ℤ) ^ k * Int.floor ((b : ℝ) ^ n * alpha) : ℤ) : ℝ) := by push_cast; rfl
  rw [hc, Int.floor_sub_intCast]

theorem blockValue_nonneg (b n k : ℕ) : 0 ≤ blockValue b n k := by
  rw [blockValue_eq_floor_fract, Int.floor_nonneg]
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg b) k) (Int.fract_nonneg _)

theorem blockValue_lt {b : ℕ} (hb : 0 < b) (n k : ℕ) :
    blockValue b n k < (b : ℤ) ^ k := by
  rw [blockValue_eq_floor_fract, Int.floor_lt]
  push_cast
  have hp : (0 : ℝ) < (b : ℝ) ^ k := pow_pos (by exact_mod_cast hb) k
  simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one ((b : ℝ) ^ n * alpha)) hp

theorem digit_range {b : ℕ} (hb : 0 < b) (n : ℕ) :
    0 ≤ digit b n ∧ digit b n < b := by
  simpa [digit] using And.intro (blockValue_nonneg b n 1) (blockValue_lt hb n 1)

theorem blockValue_append (b n k l : ℕ) :
    blockValue b n (k + l) =
      (b : ℤ) ^ l * blockValue b n k + blockValue b (n + k) l := by
  unfold blockValue
  rw [pow_add]
  simp only [Nat.add_assoc]
  ring

end GoldenNormality
