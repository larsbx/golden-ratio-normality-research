import GoldenNormality.BinarySparsity

/-!
# The actual complementary quadratic irrational

The number `beta = 1 - alpha` satisfies `beta^2 - 3*beta + 1 = 0`.
Its dyadic floors, digits and fixed-width blocks are proved to be the
corresponding complements of the actual golden-ratio objects. The strict
dyadic nonintegrality needed by the floor identity follows from the existing
integer polynomial obstruction; it is not an assumed numeral convention.

The negative linear coefficient is retained. No normality or square-root
zero-count estimate follows merely from these exact source identities.
-/

namespace GoldenNormality.BinaryComplement

noncomputable def beta : ℝ := 1 - alpha

theorem beta_pos : 0 < beta := by
  unfold beta
  linarith [alpha_lt_one]

theorem beta_lt_one : beta < 1 := by
  unfold beta
  linarith [alpha_pos]

theorem beta_quadratic : beta ^ 2 - 3 * beta + 1 = 0 := by
  unfold beta
  nlinarith [alpha_quadratic]

/-- Every certified original dyadic prefix is strictly below its scaled root.
The strictness is needed to complement a floor without a dyadic exception. -/
theorem certified_original_prefix_strict_lower {N q : ℕ}
    (certificate : PrefixCertificate (2 ^ N) q) :
    (q : ℝ) < (2 : ℝ) ^ N * alpha := by
  have hbound := ((prefixCertificate_iff_bounds
    (by positivity : 0 < 2 ^ N)).mp certificate).1
  have hbound' : (q : ℝ) ≤ (2 : ℝ) ^ N * alpha := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbound
  have hstrict : (q : ℝ) ^ 2 + (2 : ℝ) ^ N * q < ((2 : ℝ) ^ N) ^ 2 := by
    exact_mod_cast binary_prefix_polynomial_lt certificate
  have hroot : ((2 : ℝ) ^ N * alpha) ^ 2 +
      (2 : ℝ) ^ N * ((2 : ℝ) ^ N * alpha) = ((2 : ℝ) ^ N) ^ 2 := by
    calc
      _ = ((2 : ℝ) ^ N) ^ 2 * (alpha ^ 2 + alpha) := by ring
      _ = ((2 : ℝ) ^ N) ^ 2 := by rw [alpha_quadratic]; ring
  by_contra hnot
  have he : (q : ℝ) = (2 : ℝ) ^ N * alpha := by linarith
  rw [← he] at hroot
  linarith

/-- No original binary scaled floor equals the scaled irrational itself. -/
theorem original_scaledFloor_strict_lower (N : ℕ) :
    (GoldenNormality.scaledFloor 2 N : ℝ) < (2 : ℝ) ^ N * alpha := by
  let q := wordValue 2 (BinaryAutomaton.powerDigits 0 N)
  have certificate : PrefixCertificate (2 ^ N) q := prefixCertificate_powerDigits N
  have hfloor : GoldenNormality.scaledFloor 2 N = (q : ℤ) := by
    have h := (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ N)).mp certificate
    simpa only [GoldenNormality.scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using h
  rw [hfloor]
  simpa only [Int.cast_natCast] using certified_original_prefix_strict_lower certificate

/-- The actual integer floor of the complementary number at a dyadic scale. -/
noncomputable def scaledFloor (n : ℕ) : ℤ := Int.floor ((2 : ℝ) ^ n * beta)

/-- Zero-based fractional digit of the actual complementary number. -/
noncomputable def digit (n : ℕ) : ℤ := scaledFloor (n + 1) - 2 * scaledFloor n

/-- A fixed-width consecutive block, retaining both its start and its width. -/
noncomputable def blockValue (start length : ℕ) : ℤ :=
  scaledFloor (start + length) - (2 : ℤ) ^ length * scaledFloor start

@[simp] theorem scaledFloor_zero : scaledFloor 0 = 0 := by
  simp only [scaledFloor, pow_zero, one_mul]
  exact Int.floor_eq_zero_iff.mpr ⟨le_of_lt beta_pos, beta_lt_one⟩

theorem scaledFloor_nonneg (n : ℕ) : 0 ≤ scaledFloor n := by
  unfold scaledFloor
  apply Int.floor_nonneg.mpr
  exact mul_nonneg (by positivity) (le_of_lt beta_pos)

theorem scaledFloor_lt (n : ℕ) : scaledFloor n < (2 : ℤ) ^ n := by
  unfold scaledFloor
  apply Int.floor_lt.mpr
  push_cast
  have h := mul_lt_mul_of_pos_left beta_lt_one (by positivity : 0 < (2 : ℝ) ^ n)
  simpa only [mul_one] using h

/-- The `-1` is forced by nonintegrality, including the scale `n = 0`. -/
theorem scaledFloor_eq_complement (n : ℕ) :
    scaledFloor n = (2 : ℤ) ^ n - 1 - GoldenNormality.scaledFloor 2 n := by
  unfold scaledFloor
  apply Int.floor_eq_iff.mpr
  have hlo := original_scaledFloor_strict_lower n
  have hhi : (2 : ℝ) ^ n * alpha < (GoldenNormality.scaledFloor 2 n : ℝ) + 1 := by
    simpa only [GoldenNormality.scaledFloor, Nat.cast_ofNat] using
      Int.lt_floor_add_one ((2 : ℝ) ^ n * alpha)
  push_cast
  unfold beta
  constructor <;> nlinarith only [hlo, hhi]

/-- A finite original prefix certificate and the exact width-aware complement
equation certify the actual complementary prefix. -/
theorem scaledFloor_of_prefix_certificate {N q r : ℕ}
    (certificate : PrefixCertificate (2 ^ N) q)
    (complement : q + r + 1 = 2 ^ N) : scaledFloor N = (r : ℤ) := by
  have hfloor : GoldenNormality.scaledFloor 2 N = (q : ℤ) := by
    have h := (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ N)).mp certificate
    simpa only [GoldenNormality.scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using h
  rw [scaledFloor_eq_complement, hfloor]
  have hsum : (q : ℤ) + r + 1 = (2 : ℤ) ^ N := by exact_mod_cast complement
  omega

theorem digit_eq_complement (n : ℕ) :
    digit n = 1 - GoldenNormality.digit 2 n := by
  simp only [digit, scaledFloor_eq_complement, GoldenNormality.digit,
    GoldenNormality.blockValue, Nat.cast_ofNat, pow_succ]
  ring

theorem blockValue_eq_complement (start length : ℕ) :
    blockValue start length =
      (2 : ℤ) ^ length - 1 - GoldenNormality.blockValue 2 start length := by
  simp only [blockValue, scaledFloor_eq_complement, GoldenNormality.blockValue,
    Nat.cast_ofNat, pow_add]
  ring

theorem digit_range (n : ℕ) : 0 ≤ digit n ∧ digit n < 2 := by
  rw [digit_eq_complement]
  have h := GoldenNormality.digit_range (by decide : 0 < 2) n
  omega

theorem blockValue_nonneg (start length : ℕ) : 0 ≤ blockValue start length := by
  rw [blockValue_eq_complement]
  have h := GoldenNormality.blockValue_lt (by decide : 0 < 2) start length
  norm_num only [Nat.cast_ofNat] at h
  omega

theorem blockValue_lt (start length : ℕ) : blockValue start length < (2 : ℤ) ^ length := by
  rw [blockValue_eq_complement]
  have h := GoldenNormality.blockValue_nonneg 2 start length
  omega

end GoldenNormality.BinaryComplement
