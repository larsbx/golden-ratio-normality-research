import GoldenNormality.BinaryComplementCarry
import GoldenNormality.BinaryComplementCounts
import GoldenNormality.BinaryRecurrence

/-! Aggregate inequalities for the signed carries of the actual binary complement. -/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

/-- The positive part of the actual carry. -/
noncomputable def positiveCarry (n : ℕ) : ℤ := max (carry n) 0

/-- Indicator for a strictly positive actual carry. -/
noncomputable def positiveCarryIndicator (n : ℕ) : ℤ := min 1 (positiveCarry n)

theorem twice_positiveCarry_le (n : ℕ) :
    2 * positiveCarry n ≤ positiveCarry (n + 1) + convolutionCoefficient n := by
  have hr := carry_recurrence n
  unfold signedCoefficient at hr
  have hd := (digit_range n).1
  have hc := convolutionCoefficient_nonneg n
  unfold positiveCarry
  rw [max_def]
  split
  · have := le_max_right (carry (n + 1)) (0 : ℤ)
    omega
  · have := le_max_left (carry (n + 1)) (0 : ℤ)
    omega

/-- A positive carry retains the linear digit term in the recurrence. -/
theorem twice_positiveCarry_add_digit_le (n : ℕ) :
    2 * positiveCarry n + 3 * (digit n * positiveCarryIndicator n) ≤
      positiveCarry (n + 1) + convolutionCoefficient n := by
  have hr := carry_recurrence n
  unfold signedCoefficient at hr
  by_cases hp : 0 < carry n
  · have h : carry (n + 1) ≤ positiveCarry (n + 1) := le_max_left _ _
    have hpos : positiveCarry n = carry n := max_eq_left (le_of_lt hp)
    have hind : positiveCarryIndicator n = 1 := by
      unfold positiveCarryIndicator
      rw [hpos]
      exact min_eq_left (by omega)
    rw [hpos, hind, mul_one]
    omega
  · have h := twice_positiveCarry_le n
    have hpos : positiveCarry n = 0 := max_eq_right (by omega)
    simpa [positiveCarryIndicator, hpos] using h

/-- The linear digit contributions survive telescoping on every interval. -/
theorem positiveCarry_sum_add_digits_le (start length : ℕ) :
    (∑ i ∈ Finset.range length, positiveCarry (start + i)) + positiveCarry start +
      3 * (∑ i ∈ Finset.range length,
        digit (start + i) * positiveCarryIndicator (start + i)) ≤
      positiveCarry (start + length) +
        ∑ i ∈ Finset.range length, convolutionCoefficient (start + i) := by
  induction length with
  | zero => simp
  | succ length ih =>
    have h := twice_positiveCarry_add_digit_le (start + length)
    simp only [Finset.sum_range_succ, Nat.add_succ]
    change 2 * positiveCarry (start + length) +
      3 * (digit (start + length) * positiveCarryIndicator (start + length)) ≤
      positiveCarry (start + length).succ + convolutionCoefficient (start + length) at h
    omega

/-- Telescoping keeps both boundaries, even for shifted and empty intervals. -/
theorem positiveCarry_sum_le (start length : ℕ) :
    (∑ i ∈ Finset.range length, positiveCarry (start + i)) + positiveCarry start ≤
      positiveCarry (start + length) +
        ∑ i ∈ Finset.range length, convolutionCoefficient (start + i) := by
  induction length with
  | zero => simp
  | succ length ih =>
    have h := twice_positiveCarry_le (start + length)
    simp only [Finset.sum_range_succ, Nat.add_succ]
    change 2 * positiveCarry (start + length) ≤
      positiveCarry (start + length).succ + convolutionCoefficient (start + length) at h
    omega

/-- The truncated convolution counts exactly the ordered pairs below the diagonal cutoff. -/
theorem convolution_sum_eq_triangle (N : ℕ) :
    (∑ n ∈ Finset.range N, convolutionCoefficient n) =
      ∑ p ∈ ((Finset.range N ×ˢ Finset.range N).filter
        (fun p : ℕ × ℕ => p.1 + p.2 + 1 < N)), digit p.1 * digit p.2 := by
  unfold convolutionCoefficient
  rw [Finset.sum_sigma']
  classical
  apply Finset.sum_bij
    (fun (p : Σ _ : ℕ, ℕ) _ => (p.2, p.1 - 1 - p.2))
  · intro a ha
    obtain ⟨hn, hi⟩ := Finset.mem_sigma.mp ha
    simp only [Finset.mem_range] at hn hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega⟩
  · intro a ha b hb hab
    obtain ⟨_, ha'⟩ := Finset.mem_sigma.mp ha
    obtain ⟨_, hb'⟩ := Finset.mem_sigma.mp hb
    simp only [Finset.mem_range] at ha' hb'
    have hleft : a.2 = b.2 := congrArg Prod.fst hab
    have hright : a.1 - 1 - a.2 = b.1 - 1 - b.2 := congrArg Prod.snd hab
    obtain ⟨a, i⟩ := a
    obtain ⟨b, j⟩ := b
    simp only at *
    have : a = b := by omega
    subst b
    subst j
    rfl
  · intro p hp
    have h := (Finset.mem_filter.mp hp).2
    refine ⟨⟨p.1 + p.2 + 1, p.1⟩, Finset.mem_sigma.mpr
      ⟨Finset.mem_range.mpr h, Finset.mem_range.mpr (by dsimp; omega)⟩, ?_⟩
    exact Prod.ext rfl (by dsimp; omega)
  · intro _ _
    rfl

/-- The omitted mass counts all ordered pairs on or above the diagonal cutoff. -/
theorem convolution_sum_add_omitted_eq_square (N : ℕ) :
    (∑ n ∈ Finset.range N, convolutionCoefficient n) +
      (∑ p ∈ ((Finset.range N ×ˢ Finset.range N).filter
        (fun p : ℕ × ℕ => N ≤ p.1 + p.2 + 1)), digit p.1 * digit p.2) =
      (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 := by
  rw [convolution_sum_eq_triangle, ← digit_sum_eq_original_zeros]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.range N ×ˢ Finset.range N) (fun p : ℕ × ℕ => p.1 + p.2 + 1 < N)
    (fun p => digit p.1 * digit p.2)
  simp only [not_lt, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul, pow_two] at hsplit ⊢
  exact hsplit

/-- The square of the count in the upper half is disjoint from the truncated
convolution. Both halves use the original source indices. -/
theorem convolution_sum_add_upper_half_square_le (N : ℕ) :
    (∑ n ∈ Finset.range N, convolutionCoefficient n) +
      ((GoldenNormality.occurrences 2 1 0 N : ℤ) -
        (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ)) ^ 2 ≤
      (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 := by
  let allPairs := Finset.range N ×ˢ Finset.range N
  let inTriangle := fun p : ℕ × ℕ => p.1 + p.2 + 1 < N
  let weight := fun p : ℕ × ℕ => digit p.1 * digit p.2
  let upper := (Finset.range N).filter (fun i => N / 2 ≤ i)
  have hupper : (∑ i ∈ upper, digit i) =
      (GoldenNormality.occurrences 2 1 0 N : ℤ) -
        (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ) := by
    rw [← digit_sum_eq_original_zeros, ← digit_sum_eq_original_zeros]
    have hfilter : ((Finset.range N).filter (fun i => ¬ N / 2 ≤ i)) =
        Finset.range (N / 2) := by
      ext i
      simp
      omega
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range N)
      (fun i => N / 2 ≤ i) digit
    rw [hfilter] at hsplit
    change (∑ i ∈ upper, digit i) + _ = _ at hsplit
    omega
  have hdisjoint : upper ×ˢ upper ⊆ allPairs.filter (fun p => ¬ inTriangle p) := by
    intro p hp
    obtain ⟨⟨hi, hlo⟩, ⟨hj, hlj⟩⟩ := (Finset.mem_product.mp hp).imp
      Finset.mem_filter.mp Finset.mem_filter.mp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, by
      dsimp [inTriangle]
      omega⟩
  have hmass := Finset.sum_le_sum_of_subset_of_nonneg (f := weight) hdisjoint
    (fun p _ _ => mul_nonneg (digit_range p.1).1 (digit_range p.2).1)
  have hsplit := Finset.sum_filter_add_sum_filter_not allPairs inTriangle weight
  have htri := (convolution_sum_eq_triangle N).le
  change _ ≤ ∑ p ∈ allPairs.filter inTriangle, weight p at htri
  have hproduct (s : Finset ℕ) :
      (∑ p ∈ s ×ˢ s, weight p) = (∑ i ∈ s, digit i) ^ 2 := by
    simp only [weight, Finset.sum_product, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
  rw [hproduct, hupper] at hmass
  change _ = ∑ p ∈ Finset.range N ×ˢ Finset.range N, weight p at hsplit
  rw [hproduct, digit_sum_eq_original_zeros] at hsplit
  exact (add_le_add htri hmass).trans_eq hsplit

theorem convolution_sum_le_square (N : ℕ) :
    (∑ n ∈ Finset.range N, convolutionCoefficient n) ≤
      (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 := by
  have h := convolution_sum_add_upper_half_square_le N
  have hn := sq_nonneg ((GoldenNormality.occurrences 2 1 0 N : ℤ) -
    (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ))
  omega

theorem positiveCarryIndicator_le (n : ℕ) : positiveCarryIndicator n ≤ positiveCarry n :=
  min_le_right _ _

theorem positiveCarry_lt_original_zeros (N : ℕ)
    (h : 0 < GoldenNormality.occurrences 2 1 0 N) :
    positiveCarry N < (GoldenNormality.occurrences 2 1 0 N : ℤ) := by
  have hc := carry_lt_digit_sum N
  rw [digit_sum_eq_original_zeros] at hc
  exact max_lt hc (by exact_mod_cast h)

/-- The number of positive carry positions is bounded by ordered pair mass
and the finite right boundary. -/
theorem positiveCarry_count_le (N : ℕ) :
    (∑ i ∈ Finset.range N, positiveCarryIndicator i) ≤
      (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 + positiveCarry N := by
  have hs := positiveCarry_sum_le 0 N
  simp only [Nat.zero_add] at hs
  have hc := convolution_sum_le_square N
  have hi := Finset.sum_le_sum (s := Finset.range N)
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  omega

private theorem digit_one_recurs (start : ℕ) :
    ∃ j : ℕ, start ≤ j ∧ j < 2 * start + 2 ∧ digit j = 1 := by
  obtain ⟨j, hl, hu, hd⟩ := binary_digit_symbol_recurs start 0 (by decide)
  exact ⟨j, hl, hu, by simp [digit_eq_complement, hd]⟩

theorem convolution_pos_of_ones {a j : ℕ}
    (ha : digit a = 1) (hj : digit j = 1) :
    0 < convolutionCoefficient (a + j + 1) := by
  unfold convolutionCoefficient
  have hmem : a ∈ Finset.range (a + j + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum
    (f := fun i => digit i * digit (a + j + 1 - 1 - i))
    (fun i _ => mul_nonneg (digit_range i).1 (digit_range _).1) hmem
  rw [show a + j + 1 - 1 - a = j by omega, ha, hj, mul_one] at hle
  omega

theorem indicator_nonneg (i : ℕ) : 0 ≤ positiveCarryIndicator i :=
  le_min (by decide) (le_max_right _ _)

theorem indicator_eq_one {i : ℕ} (h : 0 < carry i) :
    positiveCarryIndicator i = 1 := by
  unfold positiveCarryIndicator positiveCarry
  exact min_eq_left ((show 1 ≤ carry i by omega).trans (le_max_left _ _))

/-- A gap following an actual complementary one contributes at least half its
length in positive carries, up to a fixed endpoint loss. -/
theorem zero_gap_le_twice_positive_count (a length : ℕ) (ha : digit a = 1)
    (zeros : ∀ i : ℕ, a < i → i < a + 1 + length → digit i = 0) :
    (length : ℤ) ≤ 2 * (∑ i ∈ Finset.range length,
      positiveCarryIndicator (a + 1 + i)) + 3 := by
  by_cases hshort : length < 4
  · have h := Finset.sum_nonneg (s := Finset.range length)
      (fun i _ => indicator_nonneg (a + 1 + i))
    omega
  let k := (length - 4) / 2
  have hk : 2 * k + 4 ≤ length ∧ length ≤ 2 * k + 5 := by dsimp [k]; omega
  obtain ⟨j, hkj, hj, hd⟩ := digit_one_recurs k
  have hp : 0 < carry (a + j + 1) := by
    apply carry_positive_of_convolution_three_zeroes _ (convolution_pos_of_ones ha hd)
    all_goals apply zeros <;> omega
  -- The trigger position itself is positive and belongs to this interval.
  have hl : ((k + 1 : ℕ) : ℤ) ≤ ∑ i ∈ Finset.range length, positiveCarryIndicator (a + 1 + i) := by
    calc
      ((k + 1 : ℕ) : ℤ) = ∑ _i ∈ Finset.range (k + 1), (1 : ℤ) := by simp
      _ = ∑ i ∈ Finset.range (k + 1), positiveCarryIndicator (a + 1 + i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Eq.symm
        apply indicator_eq_one
        have hi' := Finset.mem_range.mp hi
        apply carry_positive_of_zero_gap (a + 1 + i) (j - i)
        · intro x hx hy
          exact zeros x (by omega) (by omega)
        · rwa [show a + 1 + i + (j - i) = a + j + 1 by omega]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega)) (fun i _ _ => indicator_nonneg (a + 1 + i))
  omega

private theorem last_one_or_all_zero (N : ℕ) :
    (∃ a < N, digit a = 1 ∧ ∀ i, a < i → i < N → digit i = 0) ∨
      (∀ i, i < N → digit i = 0) := by
  induction N with
  | zero => right; omega
  | succ N ih =>
    by_cases h : digit N = 1
    · exact Or.inl ⟨N, by omega, h, by omega⟩
    have hz : digit N = 0 := by have := digit_range N; omega
    rcases ih with ⟨a, ha, hd, hgap⟩ | hgap
    · left
      refine ⟨a, by omega, hd, ?_⟩
      intro i hai hi
      by_cases he : i = N
      · simpa [he] using hz
      · exact hgap i hai (by omega)
    · right
      intro i hi
      by_cases he : i = N
      · simpa [he] using hz
      · exact hgap i (by omega)

/-- A bound on each post-one gap transfers to the whole prefix.
The initial zero segment costs at most one position. -/
theorem prefix_gap_budget (s t C : ℕ)
    (gap : ∀ a length : ℕ, digit a = 1 →
      (∀ i : ℕ, a < i → i < a + 1 + length → digit i = 0) →
      (s : ℤ) * (length : ℤ) ≤ (t : ℤ) * (∑ i ∈ Finset.range length,
        positiveCarryIndicator (a + 1 + i)) + (C : ℤ))
    (N : ℕ) :
    (s : ℤ) * (N : ℤ) ≤ (t : ℤ) * (∑ i ∈ Finset.range N, positiveCarryIndicator i) +
      ((C : ℤ) + s) * (GoldenNormality.occurrences 2 1 0 N : ℤ) + (s : ℤ) := by
  simp only [← digit_sum_eq_original_zeros]
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases last_one_or_all_zero N with ⟨a, ha, hd, hgap⟩ | hgap
    · let length := N - (a + 1)
      have hN : a + 1 + length = N := by dsimp [length]; omega
      have hg := gap a length hd (by simpa [hN] using hgap)
      have hzero : (∑ i ∈ Finset.range length, digit (a + 1 + i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have := Finset.mem_range.mp hi
        exact hgap _ (by omega) (by omega)
      have hp := ih a ha
      have hi := indicator_nonneg a
      have hcount : (∑ i ∈ Finset.range N, positiveCarryIndicator i) =
          (∑ i ∈ Finset.range a, positiveCarryIndicator i) + positiveCarryIndicator a +
            ∑ i ∈ Finset.range length, positiveCarryIndicator (a + 1 + i) := by
        rw [← hN, Finset.sum_range_add _ (a + 1) length, Finset.sum_range_succ]
      have hdigits : (∑ i ∈ Finset.range N, digit i) =
          (∑ i ∈ Finset.range a, digit i) + 1 := by
        rw [← hN, Finset.sum_range_add _ (a + 1) length, Finset.sum_range_succ,
          hd, hzero, add_zero]
      rw [hcount, hdigits, ← hN]
      push_cast
      have hdecomp : (N : ℤ) = (a : ℤ) + 1 + (length : ℤ) := by exact_mod_cast hN.symm
      nlinarith only [hp, hg, hdecomp, mul_nonneg (Int.natCast_nonneg t) hi]
    · obtain ⟨j, _, hj, hd⟩ := digit_one_recurs 0
      have hN : N ≤ 1 := by
        by_contra hn
        have := hgap j (by omega)
        omega
      have hi := Finset.sum_nonneg (s := Finset.range N) (fun i _ => indicator_nonneg i)
      have hz := Finset.sum_nonneg (s := Finset.range N) (fun i _ => (digit_range i).1)
      have hn : (N : ℤ) ≤ 1 := by exact_mod_cast hN
      nlinarith only [mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg s),
        mul_nonneg (Int.natCast_nonneg t) hi,
        mul_nonneg (by positivity : 0 ≤ (C : ℤ) + s) hz]

/-- Partition a prefix at its last complementary one and apply the gap bound
recursively. An initial zero segment costs at most one position. -/
theorem prefix_le_positive_count_and_zeros (N : ℕ) :
    (N : ℤ) ≤ 2 * (∑ i ∈ Finset.range N, positiveCarryIndicator i) +
      4 * (GoldenNormality.occurrences 2 1 0 N : ℤ) + 1 := by
  have hg (a length : ℕ) (ha : digit a = 1)
      (hz : ∀ i : ℕ, a < i → i < a + 1 + length → digit i = 0) :
      ((1 : ℕ) : ℤ) * (length : ℤ) ≤ ((2 : ℕ) : ℤ) *
        (∑ i ∈ Finset.range length, positiveCarryIndicator (a + 1 + i)) +
          ((3 : ℕ) : ℤ) := by
    simpa using zero_gap_le_twice_positive_count a length ha hz
  simpa using prefix_gap_budget 1 2 3 hg N

/-- An explicit square-root-scale lower bound on the actual original zero count.
The bound applies to every prefix of length at least two. -/
theorem original_zero_count_quadratic_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) ≤ 2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 +
      6 * (GoldenNormality.occurrences 2 1 0 N : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have hc := positiveCarry_count_le N
  have hl := prefix_le_positive_count_and_zeros N
  omega

/-- A two-scale refinement of the finite zero-count bound. -/
theorem original_zero_count_half_prefix_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) + 2 * ((GoldenNormality.occurrences 2 1 0 N : ℤ) -
      (GoldenNormality.occurrences 2 1 0 (N / 2) : ℤ)) ^ 2 ≤
      2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 +
      6 * (GoldenNormality.occurrences 2 1 0 N : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have hs := positiveCarry_sum_le 0 N
  simp only [Nat.zero_add] at hs
  have hi := Finset.sum_le_sum (s := Finset.range N)
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  have hc := convolution_sum_add_upper_half_square_le N
  have hl := prefix_le_positive_count_and_zeros N
  omega

/-- The finite carry estimate with the full omitted pair mass restored. -/
theorem original_zero_count_omitted_pairs_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) + 2 * (∑ p ∈ ((Finset.range N ×ˢ Finset.range N).filter
      (fun p : ℕ × ℕ => N ≤ p.1 + p.2 + 1)), digit p.1 * digit p.2) ≤
      2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 +
      6 * (GoldenNormality.occurrences 2 1 0 N : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have hs := positiveCarry_sum_le 0 N
  simp only [Nat.zero_add] at hs
  have hi := Finset.sum_le_sum (s := Finset.range N)
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  have hc := convolution_sum_add_omitted_eq_square N
  have hl := prefix_le_positive_count_and_zeros N
  omega

/-- The omitted pair bound with the additional cost of positive carries on one digits. -/
theorem original_zero_count_linear_correction_bound (N : ℕ) (hN : 2 ≤ N) :
    (N : ℤ) + 2 * (∑ p ∈ ((Finset.range N ×ˢ Finset.range N).filter
      (fun p : ℕ × ℕ => N ≤ p.1 + p.2 + 1)), digit p.1 * digit p.2) +
      6 * (∑ i ∈ Finset.range N, digit i * positiveCarryIndicator i) ≤
      2 * (GoldenNormality.occurrences 2 1 0 N : ℤ) ^ 2 +
      6 * (GoldenNormality.occurrences 2 1 0 N : ℤ) - 1 := by
  have hz : 0 < GoldenNormality.occurrences 2 1 0 N :=
    binary_occurrences_at_least 1 0 N (by decide) (by simpa using hN)
  have hp := positiveCarry_lt_original_zeros N hz
  have hs := positiveCarry_sum_add_digits_le 0 N
  simp only [Nat.zero_add] at hs
  have hi := Finset.sum_le_sum (s := Finset.range N)
    (fun i _ => positiveCarryIndicator_le i)
  have h0 : 0 ≤ positiveCarry 0 := le_max_right _ _
  have hc := convolution_sum_add_omitted_eq_square N
  have hl := prefix_le_positive_count_and_zeros N
  omega

end GoldenNormality.BinaryComplement
