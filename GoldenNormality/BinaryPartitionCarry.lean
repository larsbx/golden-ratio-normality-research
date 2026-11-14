import GoldenNormality.BinaryAggregateCarry
import Mathlib.Data.Rat.BigOperators

/-! Bounds for the truncated digit convolution on equal-width partitions. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

private theorem sum_equal_blocks (f : ℕ → ℤ) (width blocks : ℕ) :
    (∑ i ∈ Finset.range (blocks * width), f i) =
      ∑ a ∈ Finset.range blocks, ∑ i ∈ Finset.range width, f (a * width + i) := by
  induction blocks with
  | zero => simp
  | succ blocks ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem digit_sum_block (a n : ℕ) :
    (∑ i ∈ Finset.range n, digit (a * n + i)) =
      (GoldenNormality.occurrences 2 1 0 ((a + 1) * n) : ℤ) -
        (GoldenNormality.occurrences 2 1 0 (a * n) : ℤ) := by
  rw [← digit_sum_eq_original_zeros, ← digit_sum_eq_original_zeros,
    Nat.add_mul, one_mul, Finset.sum_range_add]
  ring

/-- A row starting in block `a` can see only columns below `(blocks-a)*n`.
The digits inside each block retain their actual source indices. -/
theorem convolution_sum_le_partition (blocks n : ℕ) :
    (∑ i ∈ Finset.range (blocks * n), convolutionCoefficient i) ≤
      ∑ a ∈ Finset.range blocks,
        ((GoldenNormality.occurrences 2 1 0 ((a + 1) * n) : ℤ) -
          (GoldenNormality.occurrences 2 1 0 (a * n) : ℤ)) *
        (GoldenNormality.occurrences 2 1 0 ((blocks - a) * n) : ℤ) := by
  rw [convolution_sum_eq_triangle, Finset.sum_filter, Finset.sum_product, sum_equal_blocks _ n blocks]
  apply Finset.sum_le_sum
  intro a ha
  rw [← digit_sum_block, Finset.sum_mul, ← digit_sum_eq_original_zeros]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  have hlimit : (blocks - a) * n ≤ blocks * n :=
    Nat.mul_le_mul_right n (Nat.sub_le _ _)
  have hsplit : (blocks - a) * n + a * n = blocks * n := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt (Finset.mem_range.mp ha))]
  let weight := fun j => if a * n + i + j + 1 < blocks * n then
    digit (a * n + i) * digit j else 0
  change (∑ j ∈ Finset.range (blocks * n), weight j) ≤ _
  have he : (∑ j ∈ Finset.range (blocks * n), weight j) =
      ∑ j ∈ Finset.range ((blocks - a) * n), weight j := by
    symm
    apply Finset.sum_subset (Finset.range_mono hlimit)
    intro j _ hj
    have hj : (blocks - a) * n ≤ j := by simpa using hj
    unfold weight
    have hfalse : ¬ a * n + i + j + 1 < blocks * n := by omega
    simp [weight, hfalse]
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  unfold weight
  split
  · exact le_rfl
  · exact mul_nonneg (digit_range _).1 (digit_range _).1

/-- The gap count converts the partition estimate into a finite prefix bound. -/
theorem original_zero_count_partition_bound (blocks n : ℕ) (hN : 2 ≤ blocks * n) :
    (blocks * n : ℤ) ≤ 2 * (∑ a ∈ Finset.range blocks,
        ((GoldenNormality.occurrences 2 1 0 ((a + 1) * n) : ℤ) -
          (GoldenNormality.occurrences 2 1 0 (a * n) : ℤ)) *
        (GoldenNormality.occurrences 2 1 0 ((blocks - a) * n) : ℤ)) +
      6 * (GoldenNormality.occurrences 2 1 0 (blocks * n) : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 (blocks * n) :=
    binary_occurrences_at_least 1 0 _ (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros (blocks * n) hz
  have hs := positiveCarry_sum_le 0 (blocks * n)
  simp only [Nat.zero_add] at hs
  have hi := Finset.sum_le_sum (s := Finset.range (blocks * n))
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  have hc := convolution_sum_le_partition blocks n
  have hl := prefix_le_positive_count_and_zeros (blocks * n)
  push_cast at hl ⊢
  omega

private theorem envelope_sum_le (f g : ℕ → ℝ) (w : ℕ → ℝ) (k : ℕ)
    (hzero : f 0 = g 0)
    (hfg : ∀ i ≤ k, f i ≤ g i)
    (hw : ∀ i ≤ k, 0 ≤ w i)
    (hstep : ∀ i < k, w (i + 1) ≤ w i) :
    (∑ i ∈ Finset.range k, (f (i + 1) - f i) * w i) ≤
      (∑ i ∈ Finset.range k, (g (i + 1) - g i) * w i) := by
  have haux : ∀ m ≤ k,
      (∑ i ∈ Finset.range m, (f (i + 1) - f i) * w i) +
        (g m - f m) * w m ≤
      (∑ i ∈ Finset.range m, (g (i + 1) - g i) * w i) := by
    intro m
    induction m with
    | zero => simp [hzero]
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hprod := mul_nonneg (sub_nonneg.mpr (hfg (m + 1) hm))
        (sub_nonneg.mpr (hstep m (by omega)))
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith only [hprev, hprod]
  have hprod := mul_nonneg (sub_nonneg.mpr (hfg k le_rfl)) (hw k le_rfl)
  linarith only [haux k le_rfl, hprod]

/-- A nondecreasing envelope at all block endpoints bounds the pair budget.
The use of increments is justified by summation by parts. -/
theorem original_zero_count_partition_envelope (blocks n : ℕ) (hN : 2 ≤ blocks * n)
    (g : ℕ → ℝ) (hzero : g 0 = 0) (hmono : Monotone g)
    (hcap : ∀ i ≤ blocks, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤ g i) :
    (blocks * n : ℝ) ≤ 2 * (∑ i ∈ Finset.range blocks,
      (g (i + 1) - g i) * g (blocks - i)) + 6 * g blocks - 1 := by
  let f := fun i : ℕ => (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ)
  have hfmono : Monotone f := by
    intro i j hij
    dsimp [f]
    exact_mod_cast GoldenNormality.occurrences_monotone 2 1 0
      (Nat.mul_le_mul_right n hij)
  have hb := original_zero_count_partition_bound blocks n hN
  have hb' : (blocks * n : ℝ) ≤ 2 * (∑ i ∈ Finset.range blocks,
      (f (i + 1) - f i) * f (blocks - i)) + 6 * f blocks - 1 := by
    have he := Int.cast_le (R := ℝ).mpr hb
    simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
      Int.cast_one, Int.cast_ofNat, Int.cast_sum, Nat.cast_mul, f] using he
  have hweight : (∑ i ∈ Finset.range blocks, (f (i + 1) - f i) * f (blocks - i)) ≤
      (∑ i ∈ Finset.range blocks, (f (i + 1) - f i) * g (blocks - i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hcap _ (Nat.sub_le _ _))
      (sub_nonneg.mpr (hfmono (by omega)))
  have hsum := envelope_sum_le f g (fun i => g (blocks - i)) blocks
    (by simp [f, hzero, GoldenNormality.occurrences_zero]) hcap
    (fun i _ => by simpa only [hzero] using hmono (Nat.zero_le (blocks - i)))
    (fun i _ => hmono (by omega))
  linarith only [hb', hweight, hsum, hcap blocks le_rfl]

-- The entries are rational upper bounds for the square roots of 0 through 8.
private def eighthCap : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 1415 / 1000
  | 3 => 1733 / 1000
  | 4 => 2
  | 5 => 2237 / 1000
  | 6 => 2450 / 1000
  | 7 => 2646 / 1000
  | _ => 2829 / 1000

private theorem eighthCap_mono : Monotone eighthCap := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i < 8
  · interval_cases i <;> norm_num [eighthCap]
  · have he : eighthCap i = 2829 / 1000 := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 8 := ⟨i - 8, by omega⟩
      rfl
    have he' : eighthCap (i + 1) = 2829 / 1000 := by
      obtain ⟨j, hj⟩ : ∃ j, i + 1 = j + 8 := ⟨i + 1 - 8, by omega⟩
      rw [hj]
      rfl
    rw [he, he']

/-- The eight-checkpoint envelope gives a limsup constant of at least 0.775. -/
theorem original_zero_count_eight_window (n : ℕ) (hn : 65536 ≤ n) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ 8 ∧
      (31 / 40 : ℝ) * Real.sqrt ((i * n : ℕ) : ℝ) <
        (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) := by
  by_contra! h
  let k := Real.sqrt (n : ℝ)
  let g := fun i => (31 / 40 : ℝ) * k * (eighthCap i : ℝ)
  have hk : (256 : ℝ) ≤ k := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  have hk₀ : 0 ≤ k := by linarith
  have hg₀ : g 0 = 0 := by
    have he : eighthCap 0 = 0 := by norm_num [eighthCap]
    simp [g, he]
  have hgmono : Monotone g := by
    intro i j hij
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast eighthCap_mono hij
    · positivity
  have hcap : ∀ i ≤ 8, (GoldenNormality.occurrences 2 1 0 (i * n) : ℝ) ≤ g i := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simp [hg₀, GoldenNormality.occurrences_zero]
    have hu := h i (by omega) hi
    push_cast at hu
    rw [Real.sqrt_mul (Nat.cast_nonneg i)] at hu
    have he : Real.sqrt (i : ℝ) ≤ (eighthCap i : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      interval_cases i <;> norm_num [eighthCap]
    have ht := mul_le_mul_of_nonneg_left he (show 0 ≤ (31 / 40 : ℝ) * k by positivity)
    dsimp [g, k] at ht ⊢
    linarith only [hu, ht]
  have hb := original_zero_count_partition_envelope 8 n (by omega) g hg₀ hgmono hcap
  have hsum : (∑ i ∈ Finset.range 8, (g (i + 1) - g i) * g (8 - i)) =
      ((31 / 40 : ℝ) * k) ^ 2 * (6606938 / 1000000) := by
    have hrat : (∑ i ∈ Finset.range 8,
        (eighthCap (i + 1) - eighthCap i) * eighthCap (8 - i)) =
        (6606938 / 1000000 : ℚ) := by
      norm_num [Finset.sum_range_succ, eighthCap]
    rw [← show ((6606938 / 1000000 : ℚ) : ℝ) = (6606938 / 1000000 : ℝ) by norm_num, ← hrat]
    push_cast [Rat.cast_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [g]
    ring
  rw [hsum] at hb
  have hg8 : g 8 = (31 / 40 : ℝ) * k * (2829 / 1000) := by
    have h8 : eighthCap 8 = 2829 / 1000 := by norm_num [eighthCap]
    norm_num [g, h8]
  rw [hg8, show (n : ℝ) = k ^ 2 from (Real.sq_sqrt (Nat.cast_nonneg _)).symm] at hb
  have hprod := mul_nonneg (sub_nonneg.mpr hk) hk₀
  nlinarith only [hb, hprod, hk₀]

end GoldenNormality.BinaryComplement
