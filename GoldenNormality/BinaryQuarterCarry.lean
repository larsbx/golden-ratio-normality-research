import GoldenNormality.BinaryZeroGrowth

/-! Quarter-prefix rectangles in the exact omitted pair count. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

private theorem digit_sum_Ico (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, digit i) =
      (GoldenNormality.occurrences 2 1 0 b : ℤ) -
        (GoldenNormality.occurrences 2 1 0 a : ℤ) := by
  rw [← digit_sum_eq_original_zeros, ← digit_sum_eq_original_zeros]
  have h := Finset.sum_range_add_sum_Ico digit hab
  omega

/-- In addition to the upper-half square, the second and fourth quarters
contribute two omitted rectangles, one for each order of the pair. -/
theorem convolution_sum_add_quarter_rectangles_le (n : ℕ) :
    (∑ i ∈ Finset.range (4 * n), convolutionCoefficient i) +
      ((GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) -
        (GoldenNormality.occurrences 2 1 0 (2 * n) : ℤ)) ^ 2 +
      2 * (((GoldenNormality.occurrences 2 1 0 (2 * n) : ℤ) -
        (GoldenNormality.occurrences 2 1 0 n : ℤ)) *
        ((GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) -
          (GoldenNormality.occurrences 2 1 0 (3 * n) : ℤ))) ≤
      (GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) ^ 2 := by
  let upper := Finset.Ico (2 * n) (4 * n)
  let second := Finset.Ico n (2 * n)
  let fourth := Finset.Ico (3 * n) (4 * n)
  let weight := fun p : ℕ × ℕ => digit p.1 * digit p.2
  let A := upper ×ˢ upper
  let B := second ×ˢ fourth
  let C := fourth ×ˢ second
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h₁ := Finset.mem_Ico.mp (Finset.mem_product.mp hp).1
    have h₂ := Finset.mem_Ico.mp (Finset.mem_product.mp hq).1
    omega
  have hABC : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hq' := Finset.mem_Ico.mp (Finset.mem_product.mp hq).2
    rcases Finset.mem_union.mp hp with h | h
    · have := Finset.mem_Ico.mp (Finset.mem_product.mp h).2
      omega
    · have := Finset.mem_Ico.mp (Finset.mem_product.mp h).2
      omega
  have hsubset : (A ∪ B) ∪ C ⊆
      (Finset.range (4 * n) ×ˢ Finset.range (4 * n)).filter
        (fun p : ℕ × ℕ => 4 * n ≤ p.1 + p.2 + 1) := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · rcases Finset.mem_union.mp h with h | h
      all_goals
        obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp h
        have hi := Finset.mem_Ico.mp h₁
        have hj := Finset.mem_Ico.mp h₂
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩
    · obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp h
      have hi := Finset.mem_Ico.mp h₁
      have hj := Finset.mem_Ico.mp h₂
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg (f := weight) hsubset
    (fun p _ _ => mul_nonneg (digit_range p.1).1 (digit_range p.2).1)
  rw [Finset.sum_union hABC, Finset.sum_union hAB] at hmass
  have hproduct (s t : Finset ℕ) :
      (∑ p ∈ s ×ˢ t, weight p) = (∑ i ∈ s, digit i) * (∑ i ∈ t, digit i) := by
    simp only [weight, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul]
  dsimp only [A, B, C] at hmass
  rw [hproduct, hproduct, hproduct] at hmass
  dsimp only [upper, second, fourth, weight] at hmass
  rw [digit_sum_Ico _ _ (by omega), digit_sum_Ico _ _ (by omega),
    digit_sum_Ico _ _ (by omega)] at hmass
  have hsplit := convolution_sum_add_omitted_eq_square (4 * n)
  rw [pow_two]
  have he (x y : ℤ) : y * x = x * y := mul_comm _ _
  rw [he ((GoldenNormality.occurrences 2 1 0 (2 * n) : ℤ) -
    (GoldenNormality.occurrences 2 1 0 n : ℤ))] at hmass
  nlinarith only [hmass, hsplit]

/-- A four-checkpoint envelope with a rational constant above the
two-checkpoint limsup bound. -/
theorem original_zero_count_quarter_window_76 (n : ℕ) (hn : 262144 ≤ n) :
    ∃ m ∈ ({n, 2 * n, 3 * n, 4 * n} : Finset ℕ),
      (76 / 100 : ℝ) * Real.sqrt (m : ℝ) <
        (GoldenNormality.occurrences 2 1 0 m : ℝ) := by
  by_contra! h
  let k := Real.sqrt (n : ℝ)
  let a : ℝ := GoldenNormality.occurrences 2 1 0 n
  let b : ℝ := GoldenNormality.occurrences 2 1 0 (2 * n)
  let d : ℝ := GoldenNormality.occurrences 2 1 0 (3 * n)
  let x : ℝ := GoldenNormality.occurrences 2 1 0 (4 * n)
  let A := (76 / 100 : ℝ) * k
  let B := (1415 / 1000 : ℝ) * A
  let D := (1733 / 1000 : ℝ) * A
  let X := 2 * A
  have hk : (512 : ℝ) ≤ k :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hk₀ : 0 ≤ k := by linarith
  have ha : a ≤ A := h n (by simp)
  have hs (i : ℕ) : Real.sqrt ((i * n : ℕ) : ℝ) = Real.sqrt (i : ℝ) * k := by
    push_cast
    rw [Real.sqrt_mul (Nat.cast_nonneg i)]
  have hb : b ≤ B := by
    have hb := h (2 * n) (by simp)
    rw [hs 2, Nat.cast_ofNat] at hb
    have hr : Real.sqrt 2 ≤ (1415 / 1000 : ℝ) := Real.sqrt_le_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hr hk₀
    dsimp [b, B, A]
    linarith
  have hd : d ≤ D := by
    have hd := h (3 * n) (by simp)
    rw [hs 3, Nat.cast_ofNat] at hd
    have hr : Real.sqrt 3 ≤ (1733 / 1000 : ℝ) := Real.sqrt_le_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right hr hk₀
    dsimp [d, D, A]
    linarith
  have hx : x ≤ X := by
    have hx := h (4 * n) (by simp)
    rw [hs 4, Nat.cast_ofNat, show Real.sqrt 4 = 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      exact Real.sqrt_sq (by norm_num)] at hx
    dsimp [x, X, A]
    linarith
  have ha₀ : 0 ≤ a := Nat.cast_nonneg _
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact_mod_cast GoldenNormality.occurrences_monotone 2 1 0 (show n ≤ 2 * n by omega)
  have hbudget := convolution_sum_add_quarter_rectangles_le n
  have htel := positiveCarry_sum_le 0 (4 * n)
  simp only [Nat.zero_add] at htel
  have hi := Finset.sum_le_sum (s := Finset.range (4 * n))
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  have hz : 0 < GoldenNormality.occurrences 2 1 0 (4 * n) :=
    binary_occurrences_at_least 1 0 _ (by decide) (by norm_num; omega)
  have hp := positiveCarry_lt_original_zeros (4 * n) hz
  have hl := prefix_le_positive_count_and_zeros (4 * n)
  have hi : (4 * n : ℤ) + 2 * ((GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) -
        (GoldenNormality.occurrences 2 1 0 (2 * n) : ℤ)) ^ 2 +
      4 * (((GoldenNormality.occurrences 2 1 0 (2 * n) : ℤ) -
        (GoldenNormality.occurrences 2 1 0 n : ℤ)) *
        ((GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) -
          (GoldenNormality.occurrences 2 1 0 (3 * n) : ℤ))) ≤
      2 * (GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) ^ 2 +
        6 * (GoldenNormality.occurrences 2 1 0 (4 * n) : ℤ) - 1 := by
    push_cast at hl ⊢
    omega
  have hreal : 4 * (n : ℝ) + 2 * (x - b) ^ 2 + 4 * ((b - a) * (x - d)) ≤
      2 * x ^ 2 + 6 * x - 1 := by
    have he := Int.cast_le (R := ℝ).mpr hi
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
      Int.cast_one, Int.cast_ofNat, a, b, d, x] using he
  have h₁ := mul_nonneg ha₀ (sub_nonneg.mpr hx)
  have h₂ := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hd)
  have h₃ := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ 2 * D - B - b by dsimp [D, B, A] at hb ⊢; linarith)
  have h₄ := mul_nonneg (sub_nonneg.mpr ha)
    (show 0 ≤ X - D by dsimp [X, D, A]; linarith)
  have hbound : 4 * x * a + 4 * b * d - 2 * b ^ 2 - 4 * a * d ≤
      4 * X * A + 4 * B * D - 2 * B ^ 2 - 4 * A * D := by
    nlinarith only [h₁, h₂, h₃, h₄]
  have hn_cast : (n : ℝ) = k ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
  rw [hn_cast] at hreal
  have hk₂ := mul_nonneg (sub_nonneg.mpr hk) hk₀
  dsimp [A, B, D, X] at hbound hx
  nlinarith only [hbound, hreal, hk₂, hx, hk₀]

end GoldenNormality.BinaryComplement
