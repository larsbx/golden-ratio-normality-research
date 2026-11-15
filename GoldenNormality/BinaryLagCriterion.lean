import GoldenNormality.BinaryWeylConverse
import Mathlib.Algebra.Order.Chebyshev

/-! One-sided correlation control along arithmetic progressions of orbit shifts. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators ComplexConjugate Topology
open Filter

/-- The frequency induced by the difference between two doubling iterates. -/
def lagFrequency (h : ℤ) (L d : ℕ) : ℤ := ((2 : ℤ) ^ (L * d) - 1) * h

private noncomputable def orbitPhase (x : ℝ) (h : ℤ) (n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * x)) : ℝ) : ℂ) * Complex.I)

private theorem norm_orbitPhase (x : ℝ) (h : ℤ) (n : ℕ) :
    ‖orbitPhase x h n‖ = 1 := Complex.norm_exp_ofReal_mul_I _

private theorem orbitPhase_shift (x : ℝ) (h : ℤ) (n t : ℕ) :
    orbitPhase x ((2 : ℤ) ^ t * h) n = orbitPhase x h (n + t) := by
  unfold orbitPhase
  rw [pow_add]
  congr 1
  push_cast
  ring

private theorem orbitPhase_mul_conj (x : ℝ) (a b : ℤ) (n : ℕ) :
    orbitPhase x a n * conj (orbitPhase x b n) = orbitPhase x (a - b) n := by
  simp only [orbitPhase, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem norm_averageAt_shift_one (x : ℝ) (h : ℤ) (N : ℕ) :
    ‖averageAt x (2 * h) N - averageAt x h N‖ ≤ 2 / (N : ℝ) := by
  have hshift (n : ℕ) : orbitPhase x (2 * h) n = orbitPhase x h (n + 1) := by
    simpa only [pow_one] using orbitPhase_shift x h n 1
  have hsum : (∑ n ∈ Finset.range N, orbitPhase x (2 * h) n) + orbitPhase x h 0 =
      (∑ n ∈ Finset.range N, orbitPhase x h n) + orbitPhase x h N := by
    simp_rw [hshift]
    exact (Finset.sum_range_succ' (orbitPhase x h) N).symm.trans
      (Finset.sum_range_succ (orbitPhase x h) N)
  change ‖(∑ n ∈ Finset.range N, orbitPhase x (2 * h) n) / (N : ℂ) -
    (∑ n ∈ Finset.range N, orbitPhase x h n) / (N : ℂ)‖ ≤ _
  rw [← sub_div, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have he : (∑ n ∈ Finset.range N, orbitPhase x (2 * h) n) -
      (∑ n ∈ Finset.range N, orbitPhase x h n) =
        orbitPhase x h N - orbitPhase x h 0 := by linear_combination hsum
  rw [he]
  simpa only [norm_orbitPhase, one_add_one_eq_two] using
    norm_sub_le (orbitPhase x h N) (orbitPhase x h 0)

private theorem norm_averageAt_shift (x : ℝ) (h : ℤ) (t N : ℕ) :
    ‖averageAt x ((2 : ℤ) ^ t * h) N - averageAt x h N‖ ≤ 2 * (t : ℝ) / (N : ℝ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_assoc]
    calc
      _ ≤ ‖averageAt x (2 * ((2 : ℤ) ^ t * h)) N - averageAt x ((2 : ℤ) ^ t * h) N‖ +
            ‖averageAt x ((2 : ℤ) ^ t * h) N - averageAt x h N‖ :=
        by
          simpa only [dist_eq_norm] using (dist_triangle
            (averageAt x (2 * ((2 : ℤ) ^ t * h)) N) (averageAt x ((2 : ℤ) ^ t * h) N)
            (averageAt x h N))
      _ ≤ 2 / (N : ℝ) + 2 * (t : ℝ) / (N : ℝ) :=
        add_le_add (norm_averageAt_shift_one x _ N) ih
      _ = _ := by push_cast; ring

private theorem re_averageAt_sub_le (x : ℝ) (h : ℤ) (t N : ℕ) :
    (averageAt x ((2 : ℤ) ^ t * h) N).re ≤
      (averageAt x h N).re + 2 * (t : ℝ) / (N : ℝ) := by
  have hr := Complex.re_le_norm (averageAt x ((2 : ℤ) ^ t * h) N - averageAt x h N)
  rw [Complex.sub_re] at hr
  linarith only [hr, norm_averageAt_shift x h t N]

private theorem norm_sum_sq_eq_pair_re (N : ℕ) (z : ℕ → ℂ) :
    ‖∑ i ∈ Finset.range N, z i‖ ^ 2 =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (z i * conj (z j)).re := by
  have hm := congrArg Complex.re (Complex.mul_conj' (∑ i ∈ Finset.range N, z i))
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hm
  rw [← hm, map_sum, Finset.sum_mul]
  simp only [Finset.mul_sum, Complex.re_sum]

private theorem re_sum_pair_swap (z w : ℂ) : (z * conj w).re = (w * conj z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem energy_bound (N H : ℕ) (z : ℕ → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hunit : ∀ i n, ‖z i n‖ = 1)
    (hcross : ∀ i < H, ∀ j < H, i ≠ j →
      (∑ n ∈ Finset.range N, (z i n * conj (z j n)).re) ≤ (N : ℝ) * B) :
    (∑ n ∈ Finset.range N, ‖∑ i ∈ Finset.range H, z i n‖ ^ 2) ≤
      (H : ℝ) * N + (H : ℝ) ^ 2 * (N : ℝ) * B := by
  calc
    _ = ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          ∑ n ∈ Finset.range N, (z i n * conj (z j n)).re := by
      simp_rw [norm_sum_sq_eq_pair_re]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ ≤ ∑ i ∈ Finset.range H, ∑ j ∈ Finset.range H,
          ((if i = j then (N : ℝ) else 0) + (N : ℝ) * B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simp only [Complex.mul_conj', hunit, one_pow, Complex.ofReal_one, Complex.one_re,
          Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, ite_true]
        exact le_add_of_nonneg_right (by positivity)
      · simpa only [ite_eq_right hij, zero_add] using
          hcross i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
    _ = _ := by
      have hs (i : ℕ) (hi : i ∈ Finset.range H) :
          (∑ j ∈ Finset.range H, ((if i = j then (N : ℝ) else 0) + (N : ℝ) * B)) =
            N + (H : ℝ) * ((N : ℝ) * B) := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_ite_eq, hi, nsmul_eq_mul]
      rw [Finset.sum_congr rfl hs]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private noncomputable def mixedAverage (x : ℝ) (h : ℤ) (L H N : ℕ) : ℂ :=
  (∑ i ∈ Finset.range H, averageAt x ((2 : ℤ) ^ (L * i) * h) N) / (H : ℂ)

private theorem norm_mixedAverage_sq_le (x : ℝ) (h : ℤ) (L H N : ℕ) (hH : 0 < H)
    (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (hlag : ∀ d, 0 < d → d < H → (averageAt x (lagFrequency h L d) N).re ≤ η) :
    ‖mixedAverage x h L H N‖ ^ 2 ≤ 1 / (H : ℝ) + η + 2 * ((L * H : ℕ) : ℝ) / N := by
  let z (i n : ℕ) := orbitPhase x ((2 : ℤ) ^ (L * i) * h) n
  let B : ℝ := η + 2 * ((L * H : ℕ) : ℝ) / N
  have hcross (i : ℕ) (hi : i < H) (j : ℕ) (hj : j < H) (hij : j < i) :
      (∑ n ∈ Finset.range N, (z i n * conj (z j n)).re) ≤ (N : ℝ) * B := by
    have he : (2 : ℤ) ^ (L * i) * h - (2 : ℤ) ^ (L * j) * h =
        (2 : ℤ) ^ (L * j) * lagFrequency h L (i - j) := by
      rw [show L * i = L * j + L * (i - j) by
        rw [← Nat.mul_add, Nat.add_sub_of_le hij.le]]
      unfold lagFrequency
      rw [pow_add]
      ring
    simp_rw [z, orbitPhase_mul_conj, he]
    let k := (2 : ℤ) ^ (L * j) * lagFrequency h L (i - j)
    change (∑ n ∈ Finset.range N, (orbitPhase x k n).re) ≤ _
    have hind : (averageAt x k N).re =
        (∑ n ∈ Finset.range N, (orbitPhase x k n).re) / (N : ℝ) := by
      change (((∑ n ∈ Finset.range N, orbitPhase x k n) / (N : ℂ))).re = _
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.re_sum]
    have hstep := re_averageAt_sub_le x (lagFrequency h L (i - j)) (L * j) N
    change (averageAt x k N).re ≤ _ at hstep
    rw [hind] at hstep
    rw [mul_comm, ← div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)]
    have hj' : ((L * j : ℕ) : ℝ) ≤ ((L * H : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left L hj.le
    have hf : 2 * ((L * j : ℕ) : ℝ) / (N : ℝ) ≤ 2 * ((L * H : ℕ) : ℝ) / N :=
      div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    dsimp [B]
    linarith only [hstep, hf, hlag (i - j) (by omega) (by omega)]
  have henergy := energy_bound N H z B (by dsimp [B]; positivity)
    (fun i n => norm_orbitPhase x _ n) (fun i hi j hj hij => by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · simp_rw [re_sum_pair_swap (z i _) (z j _)]
        exact hcross j hj i hi hlt
      · exact hcross i hi j hj hgt)
  have hre : mixedAverage x h L H N =
      (∑ n ∈ Finset.range N, ∑ i ∈ Finset.range H, z i n) / ((N : ℂ) * (H : ℂ)) := by
    unfold mixedAverage
    change (∑ i ∈ Finset.range H, (∑ n ∈ Finset.range N, z i n) / (N : ℂ)) / (H : ℂ) = _
    rw [← Finset.sum_div, div_div, Finset.sum_comm]
  rw [hre, norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast, div_pow]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_iff₀ (by positivity)).mpr
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range N)
    (f := fun n => ‖∑ i ∈ Finset.range H, z i n‖)
  rw [Finset.card_range] at hcs
  have ht := (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (Finset.range N)
    (fun n => ∑ i ∈ Finset.range H, z i n)) 2).trans hcs
  have hfin := ht.trans (mul_le_mul_of_nonneg_left henergy hN'.le)
  calc
    _ ≤ (N : ℝ) * ((H : ℝ) * N + (H : ℝ) ^ 2 * (N : ℝ) * B) := hfin
    _ = _ := by
      dsimp [B]
      field_simp
      ring

private theorem norm_mixedAverage_sub (x : ℝ) (h : ℤ) (L H N : ℕ) (hH : 0 < H) :
    ‖mixedAverage x h L H N - averageAt x h N‖ ≤ 2 * ((L * H : ℕ) : ℝ) / (N : ℝ) := by
  have hcast : (H : ℂ) ≠ 0 := by exact_mod_cast hH.ne'
  have he : mixedAverage x h L H N - averageAt x h N =
      (∑ i ∈ Finset.range H, (averageAt x ((2 : ℤ) ^ (L * i) * h) N - averageAt x h N)) /
        (H : ℂ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_div, mul_comm]
    rw [mul_div_cancel_right₀ _ hcast]
    rfl
  rw [he, norm_div, Complex.norm_natCast]
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  apply (div_le_iff₀ hH').mpr
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ i ∈ Finset.range H, 2 * ((L * H : ℕ) : ℝ) / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hle := Nat.mul_le_mul_left L (Finset.mem_range.mp hi).le
      exact (norm_averageAt_shift x h (L * i) N).trans
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by norm_num)) (Nat.cast_nonneg _))
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- A finite bound uniform in the source, including a dyadic source that varies with the width. -/
theorem norm_averageAt_le_of_lag_upper (x : ℝ) (h : ℤ) (L H N : ℕ) (hH : 0 < H)
    (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (hlag : ∀ d, 0 < d → d < H → (averageAt x (lagFrequency h L d) N).re ≤ η) :
    ‖averageAt x h N‖ ≤ Real.sqrt (1 / (H : ℝ) + η + 2 * ((L * H : ℕ) : ℝ) / N) +
      2 * ((L * H : ℕ) : ℝ) / (N : ℝ) := by
  have hsq := norm_mixedAverage_sq_le x h L H N hH hN η hη hlag
  have hnorm := Real.le_sqrt_of_sq_le hsq
  have hd := norm_mixedAverage_sub x h L H N hH
  have ht := dist_triangle (averageAt x h N) (mixedAverage x h L H N) 0
  rw [dist_zero_right, dist_zero_right, dist_eq_norm, norm_sub_rev (averageAt x h N)] at ht
  linarith only [hnorm, hd, ht]

private theorem averageAt_exact (h : ℤ) (N : ℕ) :
    averageAt ((scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N) h N =
      dyadicModularAverage h N :=
  averageAt_dyadic (scaledFloor 2 N) h N

/-- The finite estimate applied to the exact ordered modular phases. -/
theorem norm_dyadicModularAverage_le_of_lag_upper (h : ℤ) (L H N : ℕ) (hH : 0 < H)
    (hN : 0 < N) (η : ℝ) (hη : 0 ≤ η)
    (hlag : ∀ d, 0 < d → d < H → (dyadicModularAverage (lagFrequency h L d) N).re ≤ η) :
    ‖dyadicModularAverage h N‖ ≤
      Real.sqrt (1 / (H : ℝ) + η + 2 * ((L * H : ℕ) : ℝ) / N) +
        2 * ((L * H : ℕ) : ℝ) / (N : ℝ) := by
  rw [← averageAt_exact]
  apply norm_averageAt_le_of_lag_upper _ _ _ _ _ hH hN η hη
  simpa only [averageAt_exact]

/-- Each real lag average is eventually below every positive tolerance. -/
def LagUpperZero (h : ℤ) (L : ℕ) : Prop :=
  ∀ d : ℕ, 0 < d → ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in atTop, (dyadicModularAverage (lagFrequency h L d) N).re ≤ η

/-- Real upper bounds at spaced lags imply complex cancellation at the target mode. -/
theorem tendsto_dyadicModularAverage_of_lagUpperZero (h : ℤ) (L : ℕ)
    (hc : LagUpperZero h L) : Tendsto (dyadicModularAverage h) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨H, hH⟩ := exists_nat_gt (16 / ε ^ 2)
  have hH' : (0 : ℝ) < H := lt_trans (by positivity) hH
  have hHn : 0 < H := by exact_mod_cast hH'
  let η : ℝ := ε ^ 2 / 16
  have hη : 0 < η := by dsimp [η]; positivity
  have hfirst : 1 / (H : ℝ) < η := by
    rw [div_lt_iff₀ hH']
    have he : 0 < ε ^ 2 := by positivity
    rw [div_lt_iff₀ he] at hH
    dsimp [η]
    nlinarith only [hH]
  have hlag : ∀ᶠ N : ℕ in atTop, ∀ d, 0 < d → d < H →
      (dyadicModularAverage (lagFrequency h L d) N).re ≤ η := by
    have hh : ∀ᶠ N : ℕ in atTop, ∀ d ∈ Finset.range H, 0 < d →
        (dyadicModularAverage (lagFrequency h L d) N).re ≤ η := by
      apply (eventually_all_finset (Finset.range H)).mpr
      intro d _
      by_cases hd : 0 < d
      · exact (hc d hd η hη).mono fun _ hf _ => hf
      · exact Eventually.of_forall fun _ h => (hd h).elim
    exact hh.mono fun _ hf d hd hdH => hf d (Finset.mem_range.mpr hdH) hd
  have hd : Tendsto (fun N : ℕ => 2 * ((L * H : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hδ : 0 < min η (ε / 4) := lt_min hη (by positivity)
  filter_upwards [hlag, eventually_gt_atTop (0 : ℕ), (Metric.tendsto_nhds.mp hd) _ hδ]
    with N hlagN hN he
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at he
  rw [dist_zero_right]
  apply lt_of_le_of_lt (norm_dyadicModularAverage_le_of_lag_upper h L H N hHn hN η hη.le hlagN)
  have heη := he.trans_le (min_le_left _ _)
  have heε := he.trans_le (min_le_right _ _)
  have hrad : 1 / (H : ℝ) + η + 2 * ((L * H : ℕ) : ℝ) / (N : ℝ) ≤ (ε / 2) ^ 2 := by
    dsimp [η] at hfirst heη ⊢
    nlinarith only [hfirst, heη, sq_nonneg ε]
  have hs := (Real.sqrt_le_iff.mpr ⟨by positivity, hrad⟩)
  linarith only [hs, heε, hε]

/-- A positive spacing may be chosen independently for each odd target mode. -/
theorem normalInBase_iff_spaced_lag_upper (spacing : ℤ → ℕ)
    (hspacing : ∀ h : ℤ, h % 2 = 1 → 0 < spacing h) :
    NormalInBase 2 ↔ ∀ h : ℤ, h % 2 = 1 → LagUpperZero h (spacing h) := by
  constructor
  · intro hnormal h ho d hd η hη
    have hh : h ≠ 0 := by omega
    have hpow : (1 : ℤ) < 2 ^ (spacing h * d) := by
      exact one_lt_pow₀ (by norm_num) (Nat.ne_of_gt (Nat.mul_pos (hspacing h ho) hd))
    have hmode : lagFrequency h (spacing h) d ≠ 0 :=
      mul_ne_zero (by omega) hh
    have ht := (tendsto_average_iff_dyadic_modular _).mp
      (tendsto_average_of_normalInBase hnormal _ hmode)
    exact ((Metric.tendsto_nhds.mp ht) η hη).mono fun N hN => by
      rw [dist_zero_right] at hN
      exact (Complex.re_le_norm _).trans hN.le
  · intro h
    exact normalInBase_of_dyadic_modular_cancellation
      (fun k hk => tendsto_dyadicModularAverage_of_lagUpperZero k (spacing k) (h k hk))

/-- The schedule with spacing `2^|h|` uses logarithmically many positive frequencies below a cutoff. -/
theorem normalInBase_iff_sparse_lag_upper :
    NormalInBase 2 ↔ ∀ h : ℤ, h % 2 = 1 → LagUpperZero h (2 ^ h.natAbs) :=
  normalInBase_iff_spaced_lag_upper _ (fun _ _ => by positivity)

end GoldenNormality.BinaryDyadicOrbit
