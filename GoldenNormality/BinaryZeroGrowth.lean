import GoldenNormality.BinaryAggregateCarry

/-! The half-prefix carry bound forces larger normalized counts at arbitrarily
late positions. This is a lower bound on the limsup, with no frequency claim. -/

namespace GoldenNormality.BinaryComplement

/-- For every nonnegative constant below `1 / √(2 * √2 - 1)`, there are
arbitrarily late prefixes whose original zero count exceeds that constant
times the square root of the prefix length. -/
theorem original_zero_count_exceeds_of_sq_lt (c : ℝ) (hc : 0 ≤ c)
    (hcritical : (2 * Real.sqrt 2 - 1) * c ^ 2 < 1) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt N < (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let r := Real.sqrt 2
  let δ := 1 - (2 * r - 1) * c ^ 2
  have hδ : 0 < δ := sub_pos.mpr hcritical
  have hr : 1 ≤ r := Real.one_lt_sqrt_two.le
  obtain ⟨K, hK⟩ := exists_nat_gt (6 * c * r / δ)
  let k := K + M + 1
  let n := k ^ 2
  have hm : M ≤ n := by
    have hk : M ≤ k := by dsimp [k]; omega
    have hsq : k ≤ k ^ 2 := by
      cases k <;> simp [pow_two]
    exact hk.trans hsq
  have hn : 2 ≤ 2 * n := by
    have hk : 0 < k := by dsimp [k]; omega
    have hn : 0 < n := pow_pos hk _
    omega
  let x : ℝ := GoldenNormality.occurrences 2 1 0 (2 * n)
  let y : ℝ := GoldenNormality.occurrences 2 1 0 n
  let a := c * r * (k : ℝ)
  let b := c * (k : ℝ)
  have hsqrt : Real.sqrt (n : ℝ) = k := by
    dsimp [n]
    push_cast
    exact Real.sqrt_sq (Nat.cast_nonneg _)
  have hsqrt₂ : Real.sqrt ((2 * n : ℕ) : ℝ) = r * k := by
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hsqrt]
  by_cases hy : b < y
  · exact ⟨n, hm, by simpa only [hsqrt] using hy⟩
  by_cases hx : a < x
  · refine ⟨2 * n, by omega, ?_⟩
    simpa only [hsqrt₂, a, mul_assoc] using hx
  have hxy : 4 * x * y - 2 * y ^ 2 ≤ 4 * a * b - 2 * b ^ 2 := by
    have hy₀ : 0 ≤ y := Nat.cast_nonneg _
    have hab : b ≤ a := by
      dsimp [a, b]
      calc
        c * (k : ℝ) = (c * 1) * (k : ℝ) := by ring
        _ ≤ (c * r) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hc) (Nat.cast_nonneg _)
    have h₁ := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hx)) hy₀
    have h₂ := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hy))
      (show 0 ≤ 2 * a - b - y by linarith [le_of_not_gt hy])
    nlinarith only [h₁, h₂]
  have hbudget := original_zero_count_half_prefix_bound (2 * n) hn
  rw [show 2 * n / 2 = n by omega] at hbudget
  have hreal : (2 : ℝ) * n + 2 * (x - y) ^ 2 ≤ 2 * x ^ 2 + 6 * x - 1 := by
    have he := Int.cast_le (R := ℝ).mpr hbudget
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, Int.cast_one, Int.cast_ofNat, Nat.cast_mul, Nat.cast_ofNat, x, y] using he
  have hmass : 4 * a * b - 2 * b ^ 2 = 2 * (1 - δ) * (k : ℝ) ^ 2 := by
    dsimp [a, b, δ]
    ring
  have hk : (K : ℝ) ≤ k := by exact_mod_cast (show K ≤ k by dsimp [k]; omega)
  have hlinear : 6 * a ≤ δ * (k : ℝ) ^ 2 := by
    have hsmall : 6 * c * r ≤ δ * (k : ℝ) := by
      have h := ((div_lt_iff₀ hδ).mp hK).le
      calc
        6 * c * r ≤ (K : ℝ) * δ := h
        _ ≤ (k : ℝ) * δ := mul_le_mul_of_nonneg_right hk hδ.le
        _ = δ * (k : ℝ) := mul_comm _ _
    have h := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg k)
    dsimp [a]
    nlinarith only [h]
  have hn_cast : (n : ℝ) = (k : ℝ) ^ 2 := by norm_cast
  rw [hn_cast] at hreal
  have hnonneg := mul_nonneg hδ.le (sq_nonneg (k : ℝ))
  exfalso
  nlinarith only [hreal, hxy, hmass, hlinear, le_of_not_gt hx, hnonneg]

end GoldenNormality.BinaryComplement
