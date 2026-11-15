import GoldenNormality.BinaryRationalOrbit
import GoldenNormality.BinaryRuns

/-! An ordered adjacent-pair bound and exact recurrences for the first dyadic mode. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators

/-- The frequency-one phase at a specified source and start. -/
noncomputable def phaseAt (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((2 * Real.pi * ((2 : ℝ) ^ n * x) : ℝ) : ℂ) * Complex.I)

private theorem norm_phaseAt (x : ℝ) (n : ℕ) : ‖phaseAt x n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phaseAt_succ (x : ℝ) (n : ℕ) : phaseAt x (n + 1) = phaseAt x n ^ 2 := by
  unfold phaseAt
  rw [pow_two, ← Complex.exp_add, pow_succ]
  congr 1
  push_cast
  ring

/-- The interior adjacent pairs cover each interior phase twice and each boundary once.
A unit phase in the closed left half-circle incurs a paired norm loss of at least
`2 - √2`. The count records the starting indices of these pairs. -/
theorem norm_ordered_sum_le_of_left_half {z : ℕ → ℂ} (m : ℕ)
    (hu : ∀ n, ‖z n‖ = 1) (hs : ∀ n, z (n + 1) = z n ^ 2)
    (s : Finset ℕ) (hsub : s ⊆ Finset.range m) (hleft : ∀ n ∈ s, (z n).re ≤ 0) :
    ‖∑ n ∈ Finset.range (m + 1), z n‖ + (1 - Real.sqrt 2 / 2) * (s.card : ℝ) ≤
      (m + 1 : ℕ) := by
  classical
  have hpair (n : ℕ) : ‖z n + z (n + 1)‖ = ‖z n + 1‖ := by
    rw [hs, show z n + z n ^ 2 = z n * (z n + 1) by ring, norm_mul, hu, one_mul]
  have hshort (n : ℕ) (hn : n ∈ s) : ‖z n + z (n + 1)‖ ≤ Real.sqrt 2 := by
    rw [hpair, Complex.norm_def, Complex.normSq_add, Complex.normSq_eq_norm_sq, hu]
    simp only [one_pow, map_one, mul_one]
    apply Real.sqrt_le_sqrt
    linarith [hleft n hn]
  have hbound : ∑ n ∈ Finset.range m, ‖z n + z (n + 1)‖ ≤
      ∑ n ∈ Finset.range m, ((2 : ℝ) - (if n ∈ s then 2 - Real.sqrt 2 else 0)) := by
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : n ∈ s
    · simp only [ite_eq_left hn]
      linarith [hshort n hn]
    · simpa only [ite_eq_right hn, sub_zero, hu, one_add_one_eq_two] using
        (norm_add_le (z n) (z (n + 1)))
  have hcount :
      (∑ n ∈ Finset.range m, (if n ∈ s then 2 - Real.sqrt 2 else (0 : ℝ))) =
        (s.card : ℝ) * (2 - Real.sqrt 2) := by
    rw [← Finset.sum_filter]
    have he : (Finset.range m).filter (· ∈ s) = s := by
      ext n
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hn => ⟨hsub hn, hn⟩⟩
    rw [he, Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.sum_sub_distrib, hcount, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul] at hbound
  have hcover : (2 : ℂ) * (∑ n ∈ Finset.range (m + 1), z n) =
      (∑ n ∈ Finset.range m, (z n + z (n + 1))) + (z 0 + z m) := by
    rw [Finset.sum_add_distrib, two_mul]
    have hfirst := Finset.sum_range_succ z m
    have hlast := Finset.sum_range_succ' z m
    linear_combination hfirst + hlast
  have htotal : ‖(2 : ℂ) * (∑ n ∈ Finset.range (m + 1), z n)‖ ≤
      (∑ n ∈ Finset.range m, ‖z n + z (n + 1)‖) + 2 := by
    rw [hcover]
    apply (norm_add_le _ _).trans
    exact add_le_add (norm_sum_le _ _) (by simpa only [hu, one_add_one_eq_two] using norm_add_le (z 0) (z m))
  rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at htotal
  push_cast
  linarith

private theorem scaledFloor_two_succ (n : ℕ) :
    scaledFloor 2 (n + 1) = 2 * scaledFloor 2 n + digit 2 n := by
  simp only [digit, blockValue, pow_one, Nat.cast_ofNat]
  ring

/-- The exact prefix recurrence with its signed quadratic residual. -/
theorem actual_residual_step (n : ℕ) :
    residual ((2 : ℤ) ^ (n + 1)) (scaledFloor 2 (n + 1)) =
      4 * residual ((2 : ℤ) ^ n) (scaledFloor 2 n) -
        2 * digit 2 n * (2 * scaledFloor 2 n + (2 : ℤ) ^ n) - digit 2 n ^ 2 := by
  conv_lhs => rw [scaledFloor_two_succ n, pow_succ, mul_comm ((2 : ℤ) ^ n)]
  simpa using residual_step 2 ((2 : ℤ) ^ n) (scaledFloor 2 n) (digit 2 n)

/-- The signed integer residual factors through the actual fractional part. -/
theorem actual_residual_eq_point (n : ℕ) :
    (residual ((2 : ℤ) ^ n) (scaledFloor 2 n) : ℝ) =
      point n * (2 * (scaledFloor 2 n : ℝ) + (2 : ℝ) ^ n + point n) := by
  have hx : point n + (scaledFloor 2 n : ℝ) = (2 : ℝ) ^ n * alpha :=
    Int.fract_add_floor _
  have hroot : ((2 : ℝ) ^ n * alpha) ^ 2 + (2 : ℝ) ^ n * ((2 : ℝ) ^ n * alpha) =
      ((2 : ℝ) ^ n) ^ 2 := by
    calc
      _ = ((2 : ℝ) ^ n) ^ 2 * (alpha ^ 2 + alpha) := by ring
      _ = _ := by rw [alpha_quadratic, mul_one]
  rw [← hx] at hroot
  unfold residual
  push_cast
  nlinarith only [hroot]

/-- The ratio of the signed integer residual to the derivative at the exact prefix. -/
noncomputable def residualProxy (n : ℕ) : ℝ :=
  (residual ((2 : ℤ) ^ n) (scaledFloor 2 n) : ℝ) /
    (2 * (scaledFloor 2 n : ℝ) + (2 : ℝ) ^ n)

/-- The rational proxy for each actual point has a summable pointwise error. -/
theorem actual_residual_proxy_error (n : ℕ) :
    |residualProxy n - point n| ≤ 1 / (2 : ℝ) ^ n := by
  unfold residualProxy
  let B := (2 : ℝ) ^ n
  let a := (scaledFloor 2 n : ℝ)
  let x := point n
  have hB : 0 < B := by dsimp [B]; positivity
  have ha : 0 ≤ a := by
    have hfloor : 0 ≤ scaledFloor 2 n := Int.floor_nonneg.mpr (mul_nonneg hB.le alpha_pos.le)
    change 0 ≤ (scaledFloor 2 n : ℝ)
    exact_mod_cast hfloor
  have hx₀ : 0 ≤ x := Int.fract_nonneg _
  have hx₁ : x < 1 := Int.fract_lt_one _
  change |_ / (2 * a + B) - x| ≤ 1 / B
  have hden : 0 < 2 * a + B := by positivity
  rw [actual_residual_eq_point]
  change |x * (2 * a + B + x) / (2 * a + B) - x| ≤ 1 / B
  have he : x * (2 * a + B + x) / (2 * a + B) - x = x ^ 2 / (2 * a + B) := by
    field_simp
    ring
  rw [he, abs_of_nonneg (by positivity)]
  exact (div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hx₀ (sub_nonneg.mpr hx₁.le)]) hden.le).trans
    (div_le_div_of_nonneg_left zero_le_one hB (by linarith))

/-- The fixed-frequency average at the ordered rational residual proxies. -/
noncomputable def residualProxyAverage (h : ℤ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, Complex.exp
    ((((2 * Real.pi * (h : ℝ) * residualProxy n) : ℝ) : ℂ) * Complex.I)) / (N : ℂ)

theorem norm_average_sub_residualProxyAverage_le (h : ℤ) (N : ℕ) :
    ‖average h N - residualProxyAverage h N‖ ≤ 4 * Real.pi * |(h : ℝ)| / (N : ℝ) := by
  unfold average residualProxyAverage
  rw [← sub_div, norm_div, Complex.norm_natCast, ← Finset.sum_sub_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hgeom : (∑ n ∈ Finset.range N, (1 / 2 : ℝ) ^ n) ≤ 2 := by
    rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
    rw [div_le_iff_of_neg (by norm_num : (1 / 2 : ℝ) - 1 < 0)]
    nlinarith only [pow_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) N]
  have hcoeff : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖character h n - Complex.exp
          ((((2 * Real.pi * (h : ℝ) * residualProxy n) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, 2 * Real.pi * |(h : ℝ)| * (1 / 2 : ℝ) ^ n := by
      apply Finset.sum_le_sum
      intro n _
      rw [character_eq_of_fract]
      refine (exp_phase_distance _ _).trans ?_
      rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi),
        abs_sub_comm (point n), div_pow, one_pow]
      exact mul_le_mul_of_nonneg_left (actual_residual_proxy_error n) hcoeff
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      linarith only [mul_le_mul_of_nonneg_left hgeom hcoeff]

/-- The exact modular and rational residual averages differ by a uniform numerator error. -/
theorem norm_dyadicModularAverage_sub_residualProxyAverage_le (h : ℤ) (N : ℕ) :
    ‖dyadicModularAverage h N - residualProxyAverage h N‖ ≤
      6 * Real.pi * |(h : ℝ)| / (N : ℝ) := by
  have hd : ‖dyadicModularAverage h N - average h N‖ ≤
      2 * Real.pi * |(h : ℝ)| / (N : ℝ) := by
    rw [norm_sub_rev, ← show averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N =
      dyadicModularAverage h N from averageAt_dyadic (scaledFloor 2 N) h N]
    exact norm_average_sub_dyadic_prefix_le h N
  have hp := norm_average_sub_residualProxyAverage_le h N
  calc
    _ ≤ ‖dyadicModularAverage h N - average h N‖ + ‖average h N - residualProxyAverage h N‖ := by
      rw [show dyadicModularAverage h N - residualProxyAverage h N =
        (dyadicModularAverage h N - average h N) + (average h N - residualProxyAverage h N) by ring]
      exact norm_add_le _ _
    _ ≤ 2 * Real.pi * |(h : ℝ)| / (N : ℝ) + 4 * Real.pi * |(h : ℝ)| / (N : ℝ) :=
      add_le_add hd hp
    _ = _ := by ring

/-- Truncating the actual source at the `N`th binary digit preserves every earlier floor. -/
theorem floor_dyadic_prefix {m N : ℕ} (hm : m ≤ N) :
    ⌊(2 : ℝ) ^ m * ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N)⌋ = scaledFloor 2 m := by
  let B := (2 : ℝ) ^ (N - m)
  have hB : 0 < B := by dsimp [B]; positivity
  have hscale : (2 : ℝ) ^ N = (2 : ℝ) ^ m * B := by
    dsimp [B]
    rw [← pow_add, Nat.add_sub_of_le hm]
  have hmul : ((scaledFloor 2 m * (2 : ℤ) ^ (N - m) : ℤ) : ℝ) =
      (scaledFloor 2 m : ℝ) * B := by
    simp [B]
  have hlo : scaledFloor 2 m * (2 : ℤ) ^ (N - m) ≤ scaledFloor 2 N := by
    change _ ≤ ⌊(2 : ℝ) ^ N * alpha⌋
    apply Int.le_floor.mpr
    rw [hmul, hscale]
    calc
      _ ≤ ((2 : ℝ) ^ m * alpha) * B :=
        mul_le_mul_of_nonneg_right (Int.floor_le _) hB.le
      _ = _ := by ring
  have hhi : (scaledFloor 2 N : ℝ) < ((scaledFloor 2 m : ℝ) + 1) * B := by
    calc
      _ ≤ (2 : ℝ) ^ N * alpha := Int.floor_le _
      _ = ((2 : ℝ) ^ m * alpha) * B := by rw [hscale]; ring
      _ < _ := mul_lt_mul_of_pos_right (Int.lt_floor_add_one _) hB
  have he : (2 : ℝ) ^ m * ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) =
      (scaledFloor 2 N : ℝ) / B := by
    rw [hscale]
    field_simp
  rw [he, Int.floor_eq_iff, le_div_iff₀ hB, div_lt_iff₀ hB]
  constructor
  · rw [← hmul]
    exact_mod_cast hlo
  · exact hhi

/-- Changes among the first `N` actual digits, counted at starts `n < N-1`. -/
noncomputable def transitionStarts (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (N - 1)).filter (fun n => blockValue 2 n 2 = 1 ∨ blockValue 2 n 2 = 2)

private theorem phaseAt_re_nonpos_of_block {x : ℝ} {n : ℕ}
    (hb : (⌊(2 : ℝ) ^ (n + 2) * x⌋ : ℤ) - 4 * ⌊(2 : ℝ) ^ n * x⌋ = 1 ∨
      (⌊(2 : ℝ) ^ (n + 2) * x⌋ : ℤ) - 4 * ⌊(2 : ℝ) ^ n * x⌋ = 2) :
    (phaseAt x n).re ≤ 0 := by
  let y := (2 : ℝ) ^ n * x
  let t := Int.fract y
  have hf : (⌊4 * t⌋ : ℤ) = ⌊(2 : ℝ) ^ (n + 2) * x⌋ - 4 * ⌊(2 : ℝ) ^ n * x⌋ := by
    change ⌊4 * (y - (⌊y⌋ : ℝ))⌋ = _
    rw [mul_sub, show 4 * y = (2 : ℝ) ^ (n + 2) * x by dsimp [y]; rw [pow_add]; ring,
      show 4 * (⌊y⌋ : ℝ) = ((4 * ⌊y⌋ : ℤ) : ℝ) by push_cast; ring,
      Int.floor_sub_intCast]
  have hm : (⌊4 * t⌋ : ℤ) = 1 ∨ (⌊4 * t⌋ : ℤ) = 2 := by rwa [hf]
  have ht : 1 / 4 ≤ t ∧ t ≤ 3 / 4 := by
    rcases hm with h | h
    all_goals
      have hh := Int.floor_eq_iff.mp h
      norm_num at hh
      constructor <;> linarith
  have he : phaseAt x n = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    unfold phaseAt
    change Complex.exp (((2 * Real.pi * y : ℝ) : ℂ) * Complex.I) = _
    have hy : y = t + (⌊y⌋ : ℝ) := (Int.fract_add_floor y).symm
    conv_lhs => rw [hy, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
    have hp : (((2 * Real.pi * (⌊y⌋ : ℝ) : ℝ) : ℂ) * Complex.I) =
        (⌊y⌋ : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by push_cast; ring
    rw [hp, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [he, Complex.exp_ofReal_mul_I_re]
  apply Real.cos_nonpos_of_pi_div_two_le_of_le
  · nlinarith [mul_le_mul_of_nonneg_left ht.1 Real.pi_pos.le]
  · nlinarith [mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le]

/-- Every counted pair lies inside the prefix, giving a bound directly on the modular sum. -/
theorem norm_dyadicModularAverage_one_mul_add_transition_le (N : ℕ) :
    (N : ℝ) * ‖dyadicModularAverage 1 N‖ +
      (1 - Real.sqrt 2 / 2) * ((transitionStarts N).card : ℝ) ≤ (N : ℝ) := by
  classical
  cases N with
  | zero => simp [transitionStarts]
  | succ m =>
    let x := (scaledFloor 2 (m + 1) : ℝ) / (2 : ℝ) ^ (m + 1)
    have hs : transitionStarts (m + 1) ⊆ Finset.range m := by
      simpa only [transitionStarts, Nat.add_sub_cancel] using
        (Finset.filter_subset _ (Finset.range m))
    have hp (n : ℕ) (hn : n ∈ transitionStarts (m + 1)) : (phaseAt x n).re ≤ 0 := by
      have hn' := Finset.mem_filter.mp hn
      have hnm : n < m := by simpa using hn'.1
      apply phaseAt_re_nonpos_of_block
      dsimp [x]
      rw [floor_dyadic_prefix (by omega : n + 2 ≤ m + 1),
        floor_dyadic_prefix (by omega : n ≤ m + 1)]
      simpa only [blockValue, Nat.cast_ofNat, show (2 : ℤ) ^ 2 = 4 by decide] using hn'.2
    have hb := norm_ordered_sum_le_of_left_half m (norm_phaseAt x) (phaseAt_succ x)
      (transitionStarts (m + 1)) hs hp
    have he : dyadicModularAverage 1 (m + 1) = (∑ n ∈ Finset.range (m + 1), phaseAt x n) /
        ((m + 1 : ℕ) : ℂ) := by
      rw [← show averageAt x 1 (m + 1) = dyadicModularAverage 1 (m + 1) from
        averageAt_dyadic _ _ _]
      simp [averageAt, phaseAt]
    rw [he, norm_div, Complex.norm_natCast, mul_div_cancel₀ _ (by positivity)]
    exact hb

/-- The integer residual comparison selects the next actual binary digit. -/
theorem actual_digit_eq_one_iff_residual (n : ℕ) :
    digit 2 n = 1 ↔
      2 * (2 * scaledFloor 2 n + (2 : ℤ) ^ n) + 1 ≤
        4 * residual ((2 : ℤ) ^ n) (scaledFloor 2 n) := by
  have hstep := actual_residual_step n
  have hd := digit_range (by decide : 0 < (2 : ℕ)) n
  have hq : (0 : ℤ) ≤ scaledFloor 2 (n + 1) := by
    change 0 ≤ ⌊(2 : ℝ) ^ (n + 1) * alpha⌋
    exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) alpha_pos.le)
  have hcert : PrefixCertificate (2 ^ (n + 1)) (scaledFloor 2 (n + 1)).toNat := by
    apply (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ (n + 1))).mpr
    rw [Int.toNat_of_nonneg hq]
    simp only [scaledFloor, Nat.cast_pow, Nat.cast_ofNat]
  have hbounds := (prefixCertificate_iff_residual _ _).mp hcert
  push_cast at hbounds
  rw [Int.toNat_of_nonneg hq] at hbounds
  constructor
  · intro h
    rw [h] at hstep
    nlinarith only [hbounds.1, hstep]
  · intro h
    by_contra hne
    have hz : digit 2 n = 0 := by omega
    simp [hz] at hstep
    have hcap := hbounds.2
    rw [hstep, scaledFloor_two_succ n, hz, pow_succ] at hcap
    nlinarith only [hcap, h]

private theorem block_transition_iff (i : ℕ) :
    (blockValue 2 i 2 = 1 ∨ blockValue 2 i 2 = 2) ↔ digit 2 i ≠ digit 2 (i + 1) := by
  have hb := blockValue_append 2 i 1 1
  change blockValue 2 i 2 = (2 : ℤ) ^ 1 * digit 2 i + digit 2 (i + 1) at hb
  rw [pow_one] at hb
  have hi := digit_range (by decide : 0 < (2 : ℕ)) i
  have hj := digit_range (by decide : 0 < (2 : ℕ)) (i + 1)
  omega

private theorem exists_transition_in_window (start : ℕ) :
    ∃ i, start ≤ i ∧ i < 2 * start + 1 ∧ digit 2 i ≠ digit 2 (i + 1) := by
  by_contra! h
  have heq (k : ℕ) (hk : k < start + 2) : digit 2 (start + k) = digit 2 start := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hs := h (start + k) (by omega) (by omega)
      exact hs.symm.trans (ih (by omega))
  have heq_digit (d : ℕ) (hd : d < 2) : (d : ℤ) = digit 2 start := by
    have hm := binary_actual_window_contains start d hd
    simp only [actualDigits, List.mem_map, List.mem_range] at hm
    obtain ⟨i, hi, he⟩ := hm
    rw [heq i hi] at he
    have hnonneg := (digit_range (by decide : 0 < (2 : ℕ)) start).1
    rw [← he, Int.toNat_of_nonneg hnonneg]
  have hzero := heq_digit 0 (by decide)
  have hone := heq_digit 1 (by decide)
  omega

/-- The windows with endpoints `2^j-1` and `2^(j+1)-1` contribute
distinct transitions when both endpoints lie in the prefix. -/
theorem transitionStarts_card_ge_of_pow_le (k N : ℕ) (hN : 2 ^ k ≤ N) :
    k ≤ (transitionStarts N).card := by
  classical
  induction k generalizing N with
  | zero => omega
  | succ k ih =>
    let B : ℕ := 2 ^ k
    have hB : 0 < B := by dsimp [B]; positivity
    have h2B : 2 * B ≤ N := by simpa [B, pow_succ, Nat.mul_comm] using hN
    obtain ⟨j, hjlo, hjhi, hjdiff⟩ := exists_transition_in_window (B - 1)
    have hj : j ∈ transitionStarts N := by
      simp only [transitionStarts, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, (block_transition_iff j).mpr hjdiff⟩
    have hnew : j ∉ transitionStarts B := by
      simp only [transitionStarts, Finset.mem_filter, Finset.mem_range]
      omega
    have hsub : insert j (transitionStarts B) ⊆ transitionStarts N := by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hj
      · simp only [transitionStarts, Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact ⟨by omega, hi.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnew] at hcard
    have hprev := ih B le_rfl
    omega

/-- The quadratic source gives an unconditional logarithmic deficit in the
frequency-one modular sum through its explicit constant-run bound. -/
theorem norm_dyadicModularAverage_one_mul_add_log_le (k N : ℕ) (hN : 2 ^ k ≤ N) :
    (N : ℝ) * ‖dyadicModularAverage 1 N‖ + (1 - Real.sqrt 2 / 2) * (k : ℝ) ≤
      (N : ℝ) := by
  have hcount : (k : ℝ) ≤ ((transitionStarts N).card : ℝ) := by
    exact_mod_cast transitionStarts_card_ge_of_pow_le k N hN
  have hsqrt : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.mpr (by norm_num)
  have hnonneg : 0 ≤ 1 - Real.sqrt 2 / 2 := by linarith
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcount hnonneg)).trans
    (norm_dyadicModularAverage_one_mul_add_transition_le N)

end GoldenNormality.BinaryDyadicOrbit
