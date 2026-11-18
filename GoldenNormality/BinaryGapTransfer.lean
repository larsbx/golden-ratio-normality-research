import GoldenNormality.BinaryUnitCarry
import GoldenNormality.BinaryDyadicSeparation

/-! Transfer from local complementary recurrence to stronger aggregate bounds. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

/-- An affine upper bound for the next complementary one, measured from the
origin. For positive integers (A≥B), a witness in ([m,(A/B)m+D/B]) suffices. -/
def AffineOneRecurrence (A B D : ℕ) : Prop :=
  ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧ B * j ≤ A * m + D ∧ digit j = 1

/-- The existing elementary recurrence is one instance of the hypothesis. -/
theorem affineOneRecurrence_two : AffineOneRecurrence 2 1 1 := by
  intro m
  obtain ⟨j, hj, hupper, hzero⟩ := binary_digit_symbol_recurs m 0 (by decide)
  exact ⟨j, hj, by omega, by simp [digit_eq_complement, hzero]⟩

private theorem gap_budget_of_affine_recurrence (A B D : ℕ) (hA : 0 < A)
    (hB : 0 < B) (hr : AffineOneRecurrence A B D)
    (a length : ℕ) (ha : digit a = 1)
    (zeros : ∀ i : ℕ, a < i → i < a + 1 + length → digit i = 0) :
    (B : ℤ) * (length : ℤ) ≤ (A : ℤ) * (∑ i ∈ Finset.range length,
      positiveCarryIndicator (a + 1 + i)) + ((3 * B + D : ℕ) : ℤ) := by
  let X := B * (length - 3) - D
  let m := X / A
  by_cases hshort : B * length ≤ 3 * B + D
  · have hs := Finset.sum_nonneg (s := Finset.range length)
      (fun i _ => indicator_nonneg (a + 1 + i))
    push_cast
    have hl : (B : ℤ) * length ≤ 3 * (B : ℤ) + D := by exact_mod_cast hshort
    nlinarith only [hl, mul_nonneg (Int.natCast_nonneg A) hs]
  have hlong : 3 ≤ length := by
    by_contra! hl
    have hle := Nat.mul_le_mul_left B (show length ≤ 3 by omega)
    rw [mul_comm B 3] at hle
    omega
  have hX : X + D = B * (length - 3) := by
    have he := Nat.mul_sub_left_distrib B length 3
    rw [mul_comm B 3] at he
    dsimp [X]
    omega
  have hm : A * m ≤ X := Nat.mul_div_le X A
  have hm' : X < A * (m + 1) := by
    simpa only [m, Nat.succ_eq_add_one, mul_comm A] using
      (Nat.div_lt_iff_lt_mul hA).mp (Nat.lt_succ_self (X / A))
  obtain ⟨j, hj, hbound, hd⟩ := hr m
  have hjbound : j ≤ length - 3 := by
    apply Nat.le_of_mul_le_mul_left _ hB
    omega
  have hp : 0 < carry (a + j + 1) := by
    apply carry_positive_of_convolution_three_zeroes _ (convolution_pos_of_ones ha hd)
    all_goals exact zeros _ (by omega) (by omega)
  have hjpos : ((j + 1 : ℕ) : ℤ) ≤ ∑ i ∈ Finset.range length,
      positiveCarryIndicator (a + 1 + i) := by
    calc
      ((j + 1 : ℕ) : ℤ) = ∑ _i ∈ Finset.range (j + 1), (1 : ℤ) := by simp
      _ = ∑ i ∈ Finset.range (j + 1), positiveCarryIndicator (a + 1 + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        have hleft : 0 < carry (a + 1 + i) := by
          apply carry_positive_of_zero_gap (a + 1 + i) (j - i)
          · intro x hx hy
            exact zeros x (by omega) (by omega)
          · rwa [show a + 1 + i + (j - i) = a + j + 1 by omega]
        exact (indicator_eq_one hleft).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun i _ _ => indicator_nonneg _)
  have hl : B * length ≤ A * (j + 1) + (3 * B + D) := by
    have he := Nat.mul_sub_left_distrib B length 3
    rw [mul_comm B 3] at he
    have hle := Nat.mul_le_mul_left A (show m + 1 ≤ j + 1 by omega)
    omega
  have hcast : (B : ℤ) * length ≤ (A : ℤ) * (↑(j + 1) : ℤ) +
      ((3 * B + D : ℕ) : ℤ) := by exact_mod_cast hl
  exact hcast.trans (add_le_add_left (mul_le_mul_of_nonneg_left hjpos (Int.natCast_nonneg A)) _)

/-- The leading truncated convolution coefficient becomes (A/(2B)),
with no changes to the underlying digit or carry definitions. -/
theorem convolution_budget_of_affine_recurrence (A B D : ℕ) (hA : 0 < A)
    (hB : 0 < B) (hr : AffineOneRecurrence A B D) (N : ℕ) :
    2 * (B : ℤ) * (N : ℤ) ≤ (A : ℤ) * (∑ i ∈ Finset.range N,
      convolutionCoefficient i) +
      (3 * (A : ℤ) + 8 * (B : ℤ) + 2 * (D : ℤ)) *
        (GoldenNormality.occurrences 2 1 0 N : ℤ) + 2 * (B : ℤ) := by
  have hg := prefix_gap_budget B A (3 * B + D)
    (gap_budget_of_affine_recurrence A B D hA hB hr) N
  have hc := positiveCarry_sum_le 0 N
  have hzero : positiveCarry 0 = 0 := by simp [positiveCarry]
  simp only [Nat.zero_add, hzero, add_zero] at hc
  have hu := unitCarry_sum_le N
  have hm := twice_positive_count_le_mass_add_units N
  have ht : positiveCarry N ≤ (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
    rw [← digit_sum_eq_original_zeros]
    exact max_le (carry_lt_digit_sum N).le
      (Finset.sum_nonneg fun i _ => (digit_range i).1)
  push_cast at hg
  have hAC := Int.natCast_nonneg A
  have hstep := mul_le_mul_of_nonneg_left (show
      2 * (∑ i ∈ Finset.range N, positiveCarryIndicator i) ≤
        (∑ i ∈ Finset.range N, convolutionCoefficient i) +
          3 * (GoldenNormality.occurrences 2 1 0 N : ℤ) by omega) hAC
  nlinarith only [hg, hstep]

/-- The conditional bound holds at every sufficiently large prefix. -/
theorem zero_count_eventually_exceeds_of_affine_recurrence (A B D : ℕ) (hA : 0 < A)
    (hB : 0 < B) (hr : AffineOneRecurrence A B D) (c : ℝ) (hc : 0 ≤ c)
    (hcritical : (A : ℝ) * c ^ 2 < 2 * (B : ℝ)) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let C : ℝ := 3 * (A : ℝ) + 10 * (B : ℝ) + 2 * (D : ℝ)
  let δ : ℝ := 2 * (B : ℝ) - (A : ℝ) * c ^ 2
  have hδ : 0 < δ := sub_pos.mpr hcritical
  have hC : 0 ≤ C := by dsimp [C]; positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (C * c / δ + 1)
  refine ⟨max 2 (k ^ 2), ?_⟩
  intro N hN
  have hN2 := (le_max_left 2 (k ^ 2)).trans hN
  have hz : 1 ≤ GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN2)
  let z : ℝ := GoldenNormality.occurrences 2 1 0 N
  let t := Real.sqrt (N : ℝ)
  have ht : 0 < t := Real.sqrt_pos_of_pos (by exact_mod_cast (show 0 < N by omega))
  have hkt : (k : ℝ) ≤ t :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast (le_max_right 2 (k ^ 2)).trans hN)
  have hct : 0 ≤ c * t := mul_nonneg hc ht.le
  have hmargin : C * c < δ * t := by
    have h := (div_lt_iff₀ hδ).mp (show C * c / δ < t by linarith only [hk, hkt])
    simpa only [mul_comm t δ] using h
  have hs := Int.cast_le (R := ℝ).mpr (convolution_sum_le_square N)
  push_cast at hs
  have hA₀ : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
  have hB₀ : 0 ≤ (B : ℝ) := Nat.cast_nonneg B
  have hp := mul_le_mul_of_nonneg_left hs hA₀
  have hh := Int.cast_le (R := ℝ).mpr (convolution_budget_of_affine_recurrence A B D hA hB hr N)
  push_cast at hh
  have hz1 : (1 : ℝ) ≤ z := by
    dsimp [z]
    exact_mod_cast hz
  have hb : 2 * (B : ℝ) * N ≤ (A : ℝ) * z ^ 2 + C * z := by
    have htail := mul_le_mul_of_nonneg_left hz1 (show 0 ≤ 2 * (B : ℝ) by positivity)
    dsimp [C, z] at *
    nlinarith only [hh, hp, htail]
  by_contra! hnot
  have hh := mul_le_mul_of_nonneg_left hnot hC
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hpow : z ^ 2 ≤ (c * t) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hnot) (add_nonneg hz0 hct)]
  have hsq := mul_le_mul_of_nonneg_left
    hpow hA₀
  have hn : (N : ℝ) = t ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
  rw [hn] at hb
  have hcontra := mul_lt_mul_of_pos_right hmargin ht
  dsimp [δ] at hcontra
  nlinarith only [hb, hh, hsq, hcontra]

/-- The stronger recurrence also improves the conditional limsup constant
to `sqrt (8 * B / (π * A))`. -/
theorem zero_count_exceeds_of_affine_recurrence (A B D : ℕ) (hA : 0 < A)
    (hB : 0 < B) (hr : AffineOneRecurrence A B D) (c : ℝ) (hc : 0 ≤ c)
    (hcritical : Real.pi * c ^ 2 < 8 * (B : ℝ) / (A : ℝ)) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  let C : ℝ := 3 * (A : ℝ) + 10 * (B : ℝ) + 2 * (D : ℝ)
  have hAr : 0 < (A : ℝ) := by exact_mod_cast hA
  have hBr : 0 < (B : ℝ) := by exact_mod_cast hB
  apply zero_count_exceeds_from_pair_budget _ (4 * C / A) (by dsimp [C]; positivity) _
    c hc hcritical M
  intro N hN
  have hz : (1 : ℝ) ≤ (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
    exact_mod_cast binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hh := Int.cast_le (R := ℝ).mpr (convolution_budget_of_affine_recurrence A B D hA hB hr N)
  push_cast at hh
  apply (le_of_mul_le_mul_right ?_ hAr)
  have hextra := mul_le_mul_of_nonneg_left hz hBr.le
  have hscale := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 4 by norm_num)
  dsimp [C]
  field_simp
  nlinarith only [hscale, hextra]

/-- A dyadic approximation lower bound on the actual source implies the
affine recurrence with the same rational slope. -/
theorem affineOneRecurrence_of_dyadic_separation (A B D : ℕ) (hAB : B ≤ A)
    (hB : 0 < B)
    (hsep : ∀ (m : ℕ) (p : ℤ),
      (2 : ℝ) ^ (B * m) ≤ |(2 : ℝ) ^ m * alpha - p| ^ B * (2 : ℝ) ^ (A * m + D)) :
    AffineOneRecurrence A B D := by
  intro m
  let length := (A * m + D) / B + 1 - m
  have hm : m ≤ (A * m + D) / B := by
    apply (Nat.le_div_iff_mul_le hB).mpr
    simpa only [mul_comm m B] using (Nat.mul_le_mul_right m hAB).trans (Nat.le_add_right _ D)
  have hlength : 0 < length := by dsimp [length]; omega
  have hsize : A * m + D < B * length + B * m := by
    have hh := (Nat.div_lt_iff_lt_mul hB).mp
      (Nat.lt_succ_self ((A * m + D) / B))
    have he : B * length + B * m = B * ((A * m + D) / B + 1) := by
      rw [← Nat.mul_add]
      congr 1
      dsimp [length]
      omega
    simpa only [mul_comm _ B, Nat.succ_eq_add_one, ← he] using hh
  by_contra! hn
  have hblock : GoldenNormality.blockValue 2 m length = (2 : ℤ) ^ length - 1 := by
    have hdigit : ∀ i < length, GoldenNormality.digit 2 (m + i) = 1 := by
      intro i hi
      have hbound : B * (m + i) ≤ A * m + D := by
        rw [mul_comm B]
        apply (Nat.le_div_iff_mul_le hB).mp
        dsimp [length] at hi
        omega
      have hnot := hn (m + i) (by omega) hbound
      have h := digit_range (m + i)
      rw [digit_eq_complement] at h hnot
      omega
    have hblocks (l : ℕ) (hl : l ≤ length) :
        GoldenNormality.blockValue 2 m l = (2 : ℤ) ^ l - 1 := by
      induction l with
      | zero => simp [GoldenNormality.blockValue]
      | succ l ih =>
        have hrec := GoldenNormality.blockValue_append 2 m l 1
        rw [show l + 1 = l.succ by omega] at hrec
        rw [hrec, show GoldenNormality.blockValue 2 (m + l) 1 =
          GoldenNormality.digit 2 (m + l) by rfl, hdigit l (by omega), ih (by omega), pow_succ]
        ring
    exact hblocks length le_rfl
  have hp := (BinaryDyadicOrbit.blockValue_eq_iff m length (2 ^ length - 1)).mp (by
    rw [hblock, Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
    push_cast
    rfl)
  have hx := Int.fract_lt_one ((2 : ℝ) ^ m * alpha)
  change BinaryDyadicOrbit.point m < 1 at hx
  have hdist : |(2 : ℝ) ^ m * alpha - (GoldenNormality.scaledFloor 2 m + 1 : ℤ)| ≤
      1 / (2 : ℝ) ^ length := by
    have he : (2 : ℝ) ^ m * alpha - (GoldenNormality.scaledFloor 2 m + 1 : ℤ) =
        BinaryDyadicOrbit.point m - 1 := by
      unfold BinaryDyadicOrbit.point GoldenNormality.scaledFloor Int.fract
      push_cast
      ring
    rw [he, abs_of_neg (sub_neg.mpr hx)]
    have hl := hp.1
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ (by decide : 0 < (2 : ℕ)))] at hl
    have hpow : (2 : ℝ) ^ length ≠ 0 := by positivity
    rw [sub_div, div_self hpow] at hl
    linarith only [hl]
  have hb := hsep m (GoldenNormality.scaledFloor 2 m + 1)
  have hc := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) hdist B) (by positivity : 0 ≤ (2 : ℝ) ^ (A * m + D))
  rw [div_pow, one_pow, ← pow_mul] at hc
  have hf : A * m + D < B * m + length * B := by
    simpa only [mul_comm length B, add_comm] using hsize
  have hlt := pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hf
  have hfin := (le_div_iff₀ (show 0 < (2 : ℝ) ^ (length * B) by positivity)).mp
    (hb.trans (hc.trans_eq (one_div_mul_eq_div _ _)))
  rw [← pow_add] at hfin
  exact (not_lt_of_ge hfin) hlt

/-- An eventual dyadic approximation bound can absorb its finite initial
exceptions into the additive term in the actual recurrence. -/
theorem exists_near_unit_recurrence_of_eventual_dyadic_separation (B : ℕ) (hB : 0 < B)
    (hsep : ∃ M : ℕ, ∀ (m : ℕ) (p : ℤ), M ≤ m →
      1 ≤ |(2 : ℝ) ^ m * alpha - p| ^ B * (2 : ℝ) ^ m) :
    ∃ D, AffineOneRecurrence (B + 1) B D := by
  obtain ⟨M, hM⟩ := hsep
  let D := (B - 1) * M + 2 * B
  refine ⟨D, affineOneRecurrence_of_dyadic_separation (B + 1) B D (by omega) hB ?_⟩
  intro m p
  let x := |(2 : ℝ) ^ m * alpha - p|
  have hfact : (B + 1) * m + D = B * m + (m + D) := by ring
  rw [hfact, pow_add]
  have hprod : 1 ≤ x ^ B * (2 : ℝ) ^ (m + D) := by
    by_cases hlate : M ≤ m
    · have hb := hM m p hlate
      change 1 ≤ x ^ B * (2 : ℝ) ^ m at hb
      have hd := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
        (show m ≤ m + D by omega)
      exact hb.trans (mul_le_mul_of_nonneg_left hd (pow_nonneg (abs_nonneg _) _))
    · have hm : m ≤ M := by omega
      have hbase : 1 ≤ x * (2 : ℝ) ^ (m + 2) := by
        have hs := BinaryDyadicOrbit.rational_separation ((2 : ℤ) ^ m) p (by positivity)
        push_cast at hs
        have ht : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
        rw [abs_of_pos ht] at hs
        change 1 ≤ x * (x + Real.sqrt 5 * (2 : ℝ) ^ m) at hs
        by_cases hsmall : x ≤ 1
        · have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
          have hs5 : Real.sqrt 5 < 3 := by
            nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
          have hr := mul_le_mul_of_nonneg_right hs5.le ht.le
          apply hs.trans
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [pow_add]
          norm_num
          linarith only [hsmall, hpow, hr]
        · rw [← one_mul (1 : ℝ)]
          exact mul_le_mul (le_of_not_ge hsmall) (one_le_pow₀ (by norm_num))
            zero_le_one (abs_nonneg _)
      have hpower := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hbase B
      rw [one_pow, mul_pow, ← pow_mul] at hpower
      have hexp : (m + 2) * B ≤ m + D := by
        have hB' : B = (B - 1) + 1 := by omega
        have h := Nat.mul_le_mul_left (B - 1) hm
        have he : m * B = (B - 1) * m + m := by
          calc
            m * B = ((B - 1) + 1) * m := by rw [← hB', mul_comm]
            _ = (B - 1) * m + m := by rw [Nat.add_mul, one_mul]
        dsimp [D]
        rw [Nat.add_mul, he]
        omega
      have ht := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hexp
      exact hpower.trans (mul_le_mul_of_nonneg_left ht (pow_nonneg (abs_nonneg _) _))
  change (2 : ℝ) ^ (B * m) ≤ x ^ B * ((2 : ℝ) ^ (B * m) * (2 : ℝ) ^ (m + D))
  rw [show x ^ B * ((2 : ℝ) ^ (B * m) * (2 : ℝ) ^ (m + D)) =
    (2 : ℝ) ^ (B * m) * (x ^ B * (2 : ℝ) ^ (m + D)) by ring]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (2 : ℝ) ^ (B * m))

/-- A family of affine recurrence bounds with slopes approaching one
gives the limiting all-prefix constant `sqrt 2`. -/
theorem zero_count_eventually_exceeds_of_near_unit_recurrence
    (hr : ∀ B : ℕ, 0 < B → ∃ D, AffineOneRecurrence (B + 1) B D)
    (c : ℝ) (hc : 0 ≤ c) (hcritical : c ^ 2 < 2) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  have hδ : 0 < 2 - c ^ 2 := sub_pos.mpr hcritical
  obtain ⟨B, hB⟩ := exists_nat_gt (c ^ 2 / (2 - c ^ 2) + 1)
  have hB' : 0 < B := by
    have hh : 0 ≤ c ^ 2 / (2 - c ^ 2) := by positivity
    exact_mod_cast (show 0 < (B : ℝ) by linarith only [hB, hh])
  obtain ⟨D, hrec⟩ := hr B hB'
  have hsize := (div_lt_iff₀ hδ).mp (show c ^ 2 / (2 - c ^ 2) < B by linarith only [hB])
  apply zero_count_eventually_exceeds_of_affine_recurrence (B + 1) B D
    (by omega) hB' hrec c hc
  push_cast
  nlinarith only [hsize]

/-- The same recurrence family gives the conditional limsup constant
`sqrt (8 / π)`. -/
theorem zero_count_exceeds_of_near_unit_recurrence
    (hr : ∀ B : ℕ, 0 < B → ∃ D, AffineOneRecurrence (B + 1) B D)
    (c : ℝ) (hc : 0 ≤ c) (hcritical : Real.pi * c ^ 2 < 8) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  have hδ : 0 < 8 - Real.pi * c ^ 2 := sub_pos.mpr hcritical
  obtain ⟨B, hB⟩ := exists_nat_gt (Real.pi * c ^ 2 / (8 - Real.pi * c ^ 2) + 1)
  have hB' : 0 < B := by
    have hh : 0 ≤ Real.pi * c ^ 2 / (8 - Real.pi * c ^ 2) := by positivity
    exact_mod_cast (show 0 < (B : ℝ) by linarith only [hB, hh])
  obtain ⟨D, hrec⟩ := hr B hB'
  have hsize := (div_lt_iff₀ hδ).mp (show Real.pi * c ^ 2 / (8 - Real.pi * c ^ 2) < B by
    linarith only [hB])
  apply zero_count_exceeds_of_affine_recurrence (B + 1) B D (by omega) hB' hrec c hc _ M
  apply (lt_div_iff₀ (show (0 : ℝ) < (↑(B + 1) : ℝ) by positivity)).mpr
  push_cast
  nlinarith only [hsize]

/-- The precise external Diophantine input used to strengthen both constants.
The threshold may depend on the positive denominator (B) of the exponent. -/
def EventualDyadicSeparation : Prop :=
  ∀ B : ℕ, 0 < B → ∃ M : ℕ, ∀ (m : ℕ) (p : ℤ), M ≤ m →
    1 ≤ |(2 : ℝ) ^ m * alpha - p| ^ B * (2 : ℝ) ^ m

theorem zero_count_eventually_exceeds_of_eventual_dyadic_separation
    (hsep : EventualDyadicSeparation) (c : ℝ) (hc : 0 ≤ c) (hcritical : c ^ 2 < 2) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  zero_count_eventually_exceeds_of_near_unit_recurrence
    (fun B hB => exists_near_unit_recurrence_of_eventual_dyadic_separation B hB (hsep B hB))
    c hc hcritical

theorem zero_count_exceeds_of_eventual_dyadic_separation (hsep : EventualDyadicSeparation)
    (c : ℝ) (hc : 0 ≤ c) (hcritical : Real.pi * c ^ 2 < 8) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  zero_count_exceeds_of_near_unit_recurrence
    (fun B hB => exists_near_unit_recurrence_of_eventual_dyadic_separation B hB (hsep B hB))
    c hc hcritical M

/-- The fixed slope (3/2) still needs an additive allowance.
The source has four original ones at positions 3 through 6. -/
theorem affineOneRecurrence_three_two_needs_offset (D : ℕ) (hD : D ≤ 4) :
    ¬ AffineOneRecurrence 3 2 D := by
  intro h
  obtain ⟨j, hj, hbound, hd⟩ := h 3
  have hfloor (n q : ℕ) (hq : PrefixCertificate (2 ^ n) q) :
      GoldenNormality.scaledFloor 2 n = (q : ℤ) := by
    simpa only [GoldenNormality.scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using
      (prefixCertificate_iff_intFloor (by positivity : 0 < (2 : ℕ) ^ n)).mp hq
  have h3 := hfloor 3 4 (by decide)
  have h4 := hfloor 4 9 (by decide)
  have h5 := hfloor 5 19 (by decide)
  have h6 := hfloor 6 39 (by decide)
  have h7 := hfloor 7 79 (by decide)
  have he : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases he with rfl | rfl | rfl | rfl <;>
    norm_num [digit_eq_complement, GoldenNormality.digit, GoldenNormality.blockValue,
      h3, h4, h5, h6, h7] at hd

end GoldenNormality.BinaryComplement
