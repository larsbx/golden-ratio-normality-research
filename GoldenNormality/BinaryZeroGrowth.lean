import GoldenNormality.BinaryAggregateCarry

/-! The half-prefix carry bound forces larger normalized counts at arbitrarily
late positions. This is a lower bound on the limsup, with no frequency claim. -/

namespace GoldenNormality.BinaryComplement

/-- Above the explicit threshold, at least one of two consecutive
doubling checkpoints exceeds the proposed square-root envelope. -/
theorem original_zero_count_doubling_pair (c : ℝ) (hc : 0 ≤ c)
    (n : ℕ) (hn : 1 ≤ n)
    (hsize : 3 * c * Real.sqrt 2 ≤ (1 - (2 * Real.sqrt 2 - 1) * c ^ 2) * Real.sqrt n) :
    c * Real.sqrt n < (GoldenNormality.occurrences 2 1 0 n : ℝ) ∨
      c * Real.sqrt ((2 * n : ℕ) : ℝ) < (GoldenNormality.occurrences 2 1 0 (2 * n) : ℝ) := by
  let r := Real.sqrt 2
  let δ := 1 - (2 * r - 1) * c ^ 2
  let k := Real.sqrt (n : ℝ)
  have hk₀ : 0 ≤ k := Real.sqrt_nonneg _
  have hr : 1 ≤ r := Real.one_lt_sqrt_two.le
  let x : ℝ := GoldenNormality.occurrences 2 1 0 (2 * n)
  let y : ℝ := GoldenNormality.occurrences 2 1 0 n
  let a := c * r * k
  let b := c * k
  have hsqrt₂ : Real.sqrt ((2 * n : ℕ) : ℝ) = r * k := by
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  by_cases hy : b < y
  · exact Or.inl hy
  by_cases hx : a < x
  · apply Or.inr
    simpa only [hsqrt₂, a, mul_assoc] using hx
  have hxy : 4 * x * y - 2 * y ^ 2 ≤ 4 * a * b - 2 * b ^ 2 := by
    have hy₀ : 0 ≤ y := Nat.cast_nonneg _
    have hab : b ≤ a := by
      dsimp [a, b]
      calc
        c * k = (c * 1) * k := by ring
        _ ≤ (c * r) * k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hc) hk₀
    have h₁ := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hx)) hy₀
    have h₂ := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hy))
      (show 0 ≤ 2 * a - b - y by linarith [le_of_not_gt hy])
    nlinarith only [h₁, h₂]
  have hbudget := original_zero_count_half_prefix_bound (2 * n) (by omega)
  rw [show 2 * n / 2 = n by omega] at hbudget
  have hreal : (2 : ℝ) * n + 2 * (x - y) ^ 2 ≤ 2 * x ^ 2 + 6 * x - 1 := by
    have he := Int.cast_le (R := ℝ).mpr hbudget
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, x, y] using he
  have hmass : 4 * a * b - 2 * b ^ 2 = 2 * (1 - δ) * k ^ 2 := by
    dsimp [a, b, δ]
    ring
  have hlinear : 6 * a ≤ 2 * δ * k ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hsize hk₀
    change (3 * c * r) * k ≤ (δ * k) * k at h
    dsimp [a]
    nlinarith only [h]
  have hn_cast : (n : ℝ) = k ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
  rw [hn_cast] at hreal
  exfalso
  nlinarith only [hreal, hxy, hmass, hlinear, le_of_not_gt hx]

/-- For every nonnegative constant below `1 / √(2 * √2 - 1)`, there are
arbitrarily late prefixes above the proposed square-root envelope. -/
theorem original_zero_count_exceeds_of_sq_lt (c : ℝ) (hc : 0 ≤ c)
    (hcritical : (2 * Real.sqrt 2 - 1) * c ^ 2 < 1) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt N < (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let δ := 1 - (2 * Real.sqrt 2 - 1) * c ^ 2
  have hδ : 0 < δ := sub_pos.mpr hcritical
  obtain ⟨K, hK⟩ := exists_nat_gt (3 * c * Real.sqrt 2 / δ)
  let k := K + M + 1
  let n := k ^ 2
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hkn : k ≤ n := by
    dsimp [n]
    simpa [pow_two] using Nat.mul_le_mul_left k hk
  have hm : M ≤ n := (show M ≤ k by dsimp [k]; omega).trans hkn
  have hsqrt : Real.sqrt (n : ℝ) = k := by
    dsimp [n]
    push_cast
    exact Real.sqrt_sq (Nat.cast_nonneg _)
  have hsize : 3 * c * Real.sqrt 2 ≤ δ * Real.sqrt n := by
    rw [hsqrt, mul_comm δ]
    exact ((div_lt_iff₀ hδ).mp hK).le.trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (show K ≤ k by dsimp [k]; omega)) hδ.le)
  rcases original_zero_count_doubling_pair c hc n (hk.trans hkn) hsize with h | h
  · exact ⟨n, hm, h⟩
  · exact ⟨2 * n, by omega, h⟩

/-- An explicit rational example of the two-checkpoint guarantee. -/
theorem original_zero_count_doubling_pair_73 (n : ℕ) (hn : 16384 ≤ n) :
    (73 / 100 : ℝ) * Real.sqrt n < (GoldenNormality.occurrences 2 1 0 n : ℝ) ∨
      (73 / 100 : ℝ) * Real.sqrt ((2 * n : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (2 * n) : ℝ) := by
  apply original_zero_count_doubling_pair _ (by norm_num) n (by omega)
  have hr : Real.sqrt 2 ≤ (1415 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr (by norm_num)
  have hs : (128 : ℝ) ≤ Real.sqrt n :=
    (Real.le_sqrt (by norm_num) (Nat.cast_nonneg n)).mpr (by exact_mod_cast hn)
  have hδ : (24793 / 1000000 : ℝ) ≤ 1 - (2 * Real.sqrt 2 - 1) * (73 / 100) ^ 2 := by
    linarith only [hr]
  have h := mul_le_mul hδ hs (by norm_num) (by linarith only [hδ])
  linarith only [h, hr]

/-- Every pair of consecutive dyadic checkpoints from exponent fourteen
onward has at least one normalized zero count strictly above 0.73. -/
theorem original_zero_count_dyadic_pair_73 (j : ℕ) (hj : 14 ≤ j) :
    (73 / 100 : ℝ) * Real.sqrt ((2 ^ j : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (2 ^ j) : ℝ) ∨
      (73 / 100 : ℝ) * Real.sqrt ((2 ^ (j + 1) : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (2 ^ (j + 1)) : ℝ) := by
  have hn : 16384 ≤ (2 : ℕ) ^ j :=
    calc
      16384 = 2 ^ 14 := by decide
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
  simpa only [pow_succ, Nat.mul_comm (2 ^ j) 2] using
    original_zero_count_doubling_pair_73 (2 ^ j) hn

end GoldenNormality.BinaryComplement
