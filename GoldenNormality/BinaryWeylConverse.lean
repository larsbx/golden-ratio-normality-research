import GoldenNormality.BinaryRationalOrbit

/-! The converse Weyl implication, using dyadic step approximations. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Topology
open Filter

private theorem count_ratio_tendsto (hn : NormalInBase 2) (k j : ℕ)
    (hk : 1 ≤ k) (hj : j < 2 ^ k) :
    Tendsto (fun N : ℕ => (cellCount k j N : ℝ) / (N : ℝ)) atTop
      (𝓝 (1 / (2 : ℝ) ^ k)) := by
  rw [normalInBase_iff_dyadic_cells] at hn
  let B := (2 : ℝ) ^ k
  have hB : 0 < B := by dsimp [B]; positivity
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨T, hT⟩ := exists_nat_gt ((1 / ε) / B + 1)
  have ht : (0 : ℝ) < T := by
    have hp : 0 ≤ (1 / ε) / B := by positivity
    linarith only [hT, hp]
  have ht' : 1 ≤ T := by exact_mod_cast (show 0 < T by exact_mod_cast ht)
  obtain ⟨M, hM, hbound⟩ := hn k hk j hj T ht'
  refine ⟨M, fun N hN => ?_⟩
  have hnpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hdist (x y : ℕ) : (Nat.dist x y : ℝ) = |(x : ℝ) - (y : ℝ)| := by
    rcases le_total x y with h | h
    · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
        abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  have hb : |B * (cellCount k j N : ℝ) - (N : ℝ)| * (T : ℝ) ≤ (N : ℝ) := by
    have hh : (Nat.dist (2 ^ k * cellCount k j N) N : ℝ) * (T : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hbound N hN
    simpa only [hdist, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, B] using hh
  have he : ((cellCount k j N : ℝ) / (N : ℝ) - 1 / B) =
      (B * (cellCount k j N : ℝ) - (N : ℝ)) / (B * (N : ℝ)) := by field_simp
  have hp : 1 / ε < B * (T : ℝ) := by
    have hh := (div_lt_iff₀ hB).mp (show (1 / ε) / B < T by linarith only [hT])
    simpa only [mul_comm (T : ℝ) B] using hh
  have hlast : 1 / (B * (T : ℝ)) < ε := by
    apply (div_lt_iff₀ (mul_pos hB ht)).mpr
    nlinarith only [(div_lt_iff₀ hε).mp hp]
  rw [Real.dist_eq, he, abs_div, abs_of_pos (mul_pos hB hnpos)]
  apply lt_of_le_of_lt _ hlast
  apply (div_le_div_iff₀ (mul_pos hB hnpos) (mul_pos hB ht)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hb hB.le]

private noncomputable def phase (h : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * (h : ℝ) * x) : ℂ) * Complex.I)

private theorem phase_lip (h : ℤ) (x y : ℝ) :
    ‖phase h x - phase h y‖ ≤ 2 * Real.pi * |(h : ℝ)| * |x - y| := by
  unfold phase
  refine (exp_phase_distance _ _).trans_eq ?_
  rw [← mul_sub, abs_mul (2 * Real.pi * (h : ℝ)), abs_mul (2 * Real.pi),
    abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

private theorem step_sum (h : ℤ) (k N : ℕ) :
    (∑ j ∈ Finset.range (2 ^ k), (cellCount k j N : ℂ) *
      phase h ((j : ℝ) / (2 : ℝ) ^ k)) =
      ∑ n ∈ Finset.range N, phase h (((blockValue 2 n k).natAbs : ℝ) / (2 : ℝ) ^ k) := by
  classical
  let a := fun n => (blockValue 2 n k).natAbs
  have ha (n : ℕ) : (a n : ℤ) = blockValue 2 n k := Int.natAbs_of_nonneg (blockValue_nonneg _ _ _)
  let f := fun n => phase h ((a n : ℝ) / (2 : ℝ) ^ k)
  have hmap (n : ℕ) (_ : n ∈ Finset.range N) : a n ∈ Finset.range (2 ^ k) := by
    apply Finset.mem_range.mpr
    have he : (a n : ℤ) < (2 : ℤ) ^ k := by rw [ha]; exact blockValue_lt (by decide) n k
    exact_mod_cast he
  change _ = ∑ n ∈ Finset.range N, f n
  rw [← Finset.sum_fiberwise_of_maps_to hmap f]
  apply Finset.sum_congr rfl
  intro j _
  have he (n : ℕ) (hn : n ∈ (Finset.range N).filter (fun x => a x = j)) :
      f n = phase h ((j : ℝ) / (2 : ℝ) ^ k) := by
    simp only [f, (Finset.mem_filter.mp hn).2]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hcard := (List.nodup_range (n := N)).card_eq_countP (P := fun n => a n = j)
  rw [List.toFinset_range] at hcard
  rw [hcard, cellCount_eq_occurrences]
  unfold occurrences
  have hh (n : ℕ) : a n = j ↔ blockValue 2 n k = (j : ℤ) := by rw [← ha, Int.natCast_inj]
  simp only [hh]

private noncomputable def stepAverage (h : ℤ) (k N : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (2 ^ k), (cellCount k j N : ℂ) *
    phase h ((j : ℝ) / (2 : ℝ) ^ k)) / (N : ℂ)

private theorem norm_sub_stepAverage (h : ℤ) (k N : ℕ) :
    ‖average h N - stepAverage h k N‖ ≤ 2 * Real.pi * |(h : ℝ)| / (2 : ℝ) ^ k := by
  have hcoef : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  by_cases hN : N = 0
  · simpa [hN, average, stepAverage, cellCount] using
      (div_nonneg hcoef (show (0 : ℝ) ≤ 2 ^ k by positivity))
  have hN' : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  rw [stepAverage, step_sum, average, ← sub_div, norm_div, Complex.norm_natCast, ← Finset.sum_sub_distrib]
  apply (div_le_iff₀ hN').mpr
  calc
    _ ≤ ∑ n ∈ Finset.range N, ‖character h n -
        phase h (((blockValue 2 n k).natAbs : ℝ) / (2 : ℝ) ^ k)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, 2 * Real.pi * |(h : ℝ)| / (2 : ℝ) ^ k := by
      apply Finset.sum_le_sum
      intro n _
      rw [character_eq_of_fract]
      change ‖phase h (point n) - phase h _‖ ≤ _
      refine (phase_lip h _ _).trans ?_
      let j := (blockValue 2 n k).natAbs
      obtain ⟨hl, hu⟩ := (blockValue_eq_iff n k j).mp
        (Int.natAbs_of_nonneg (blockValue_nonneg _ _ _)).symm
      rw [abs_of_nonneg (sub_nonneg.mpr hl), ← mul_one_div]
      apply mul_le_mul_of_nonneg_left _ hcoef
      rw [add_div] at hu
      simp only [div_eq_mul_inv, one_mul] at hu
      change point n - (j : ℝ) * (1 / (2 : ℝ) ^ k) ≤ (2 ^ k : ℝ)⁻¹
      simp only [div_eq_mul_inv, one_mul]
      linarith only [hu]
    _ = _ := by simp [mul_comm]

private theorem phase_sum_zero (h : ℤ) (hh : h ≠ 0) (q : ℕ) [NeZero q]
    (hf : h.natAbs < q) :
    ∑ j ∈ Finset.range q, phase h ((j : ℝ) / (q : ℝ)) = 0 := by
  have hz : (h : ZMod q) ≠ 0 := by
    intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd h q).mp he
    have hd' : q ∣ h.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hd
    exact (not_le_of_gt hf) (Nat.le_of_dvd (Int.natAbs_pos.mpr hh) hd')
  have hp (j : ℕ) : phase h ((j : ℝ) / (q : ℝ)) =
      ZMod.stdAddChar ((j : ZMod q) * (h : ZMod q)) := by
    unfold phase
    have he : (j : ZMod q) * (h : ZMod q) = (((j : ℤ) * h : ℤ) : ZMod q) := by
      push_cast
      rfl
    rw [he, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  simp_rw [hp]
  rw [← Fin.sum_univ_eq_sum_range]
  have hb : Function.Bijective (fun j : Fin q => (j.val : ZMod q)) := by
    constructor
    · intro i j he
      apply Fin.ext
      have hv := congrArg ZMod.val he
      simpa only [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] using hv
    · intro z
      exact ⟨⟨z.val, z.val_lt⟩, ZMod.natCast_zmod_val z⟩
  rw [Fintype.sum_equiv (Equiv.ofBijective _ hb)
    (fun j => ZMod.stdAddChar ((j.val : ZMod q) * (h : ZMod q)))
    (fun j => ZMod.stdAddChar (j * (h : ZMod q))) fun _ => rfl]
  simpa only [ite_eq_right hz, Nat.cast_zero] using
    AddChar.sum_mulShift (h : ZMod q) (ZMod.isPrimitive_stdAddChar q)

private theorem tendsto_stepAverage (hn : NormalInBase 2) (h : ℤ) (hh : h ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) (hf : h.natAbs < 2 ^ k) :
    Tendsto (stepAverage h k) atTop (𝓝 0) := by
  let B := (2 : ℝ) ^ k
  let g := fun j : ℕ => phase h ((j : ℝ) / B)
  have hlim (j : ℕ) (hj : j ∈ Finset.range (2 ^ k)) :
      Tendsto (fun N => ((cellCount k j N : ℂ) / (N : ℂ)) * g j)
        atTop (𝓝 (((1 / B : ℝ) : ℂ) * g j)) := by
    have hr := count_ratio_tendsto hn k j hk (Finset.mem_range.mp hj)
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast, B] using
      hc.mul_const (g j)
  have ht := tendsto_finsetSum (Finset.range (2 ^ k)) hlim
  have : NeZero (2 ^ k : ℕ) := ⟨by positivity⟩
  have hsum : ∑ j ∈ Finset.range (2 ^ k), g j = 0 := by
    simpa only [g, B, Nat.cast_pow, Nat.cast_ofNat] using phase_sum_zero h hh (2 ^ k) hf
  rw [← Finset.mul_sum, hsum, mul_zero] at ht
  unfold stepAverage
  simpa only [g, B, div_mul_eq_mul_div, Finset.sum_div] using ht

/-- Correct limiting frequencies of all dyadic cells force each nonzero Fourier mode to decay. -/
theorem tendsto_average_of_normalInBase (hn : NormalInBase 2) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (average h) atTop (𝓝 0) := by
  let C := 2 * Real.pi * |(h : ℝ)|
  have hf : Tendsto (fun k : ℕ => C / (2 : ℝ) ^ k) atTop (𝓝 0) := by
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 2⁻¹ by norm_num) (show (2 : ℝ)⁻¹ < 1 by norm_num)
    simpa only [inv_pow, ← div_eq_mul_inv, mul_zero] using ht.const_mul C
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hf) (ε / 2) (by positivity)
  let k := max K (h.natAbs + 1)
  have hk : 1 ≤ k := (show 1 ≤ h.natAbs + 1 by omega).trans (le_max_right _ _)
  have hpow : h.natAbs < 2 ^ k := by
    have hle : h.natAbs + 1 ≤ k := le_max_right _ _
    have hp := k.lt_two_pow_self
    omega
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp (tendsto_stepAverage hn h hh k hk hpow))
    (ε / 2) (by positivity)
  refine ⟨M, fun N hN => ?_⟩
  have hεk := hK k (le_max_left _ _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by dsimp [C]; positivity)] at hεk
  have hsmall := hM N hN
  rw [dist_zero_right] at hsmall ⊢
  have htri : ‖average h N‖ ≤ ‖average h N - stepAverage h k N‖ + ‖stepAverage h k N‖ := by
    simpa only [sub_add_cancel] using norm_add_le (average h N - stepAverage h k N) (stepAverage h k N)
  have hd := norm_sub_stepAverage h k N
  change ‖average h N - stepAverage h k N‖ ≤ C / (2 : ℝ) ^ k at hd
  linarith only [htri, hd, hεk, hsmall]

/-- The odd-mode modular condition is exactly binary normality of the actual source. -/
theorem normalInBase_iff_dyadic_modular_cancellation :
    NormalInBase 2 ↔ ∀ h : ℤ, h % 2 = 1 → Tendsto (dyadicModularAverage h) atTop (𝓝 0) := by
  constructor
  · intro hn h ho
    exact (tendsto_average_iff_dyadic_modular h).mp (tendsto_average_of_normalInBase hn h (by omega))
  · exact normalInBase_of_dyadic_modular_cancellation

end GoldenNormality.BinaryDyadicOrbit
