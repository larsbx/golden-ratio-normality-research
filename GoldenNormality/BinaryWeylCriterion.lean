import GoldenNormality.BinaryDyadicOrbit
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.MetricSpace.Equicontinuity

/-! The Weyl implication for the actual binary orbit. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Topology ENNReal
open Filter MeasureTheory Set

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

local notation "Circle₁" => AddCircle (1 : ℝ)

private noncomputable def circlePoint (n : ℕ) : Circle₁ :=
  ((2 : ℝ) ^ n * alpha : ℝ)

private noncomputable def haar : ProbabilityMeasure Circle₁ :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

private noncomputable def empirical (N : ℕ) : ProbabilityMeasure Circle₁ :=
  ⟨(↑(N + 1) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N + 1),
    Measure.dirac (circlePoint n), ⟨by
      rw [Measure.smul_apply, Measure.finsetSum_apply]
      simp [ENNReal.inv_mul_cancel]⟩⟩

private theorem integral_empirical (f : C(Circle₁, ℂ)) (N : ℕ) :
    (∫ x, f x ∂(empirical N : Measure Circle₁)) =
      (∑ n ∈ Finset.range (N + 1), f (circlePoint n)) / (↑(N + 1) : ℂ) := by
  change (∫ x, f x ∂((↑(N + 1) : ℝ≥0∞)⁻¹ •
    ∑ n ∈ Finset.range (N + 1), Measure.dirac (circlePoint n))) = _
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, integral_dirac, Complex.real_smul,
      Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  · intro n _
    exact (f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))

private theorem integral_fourier_haar (h : ℤ) :
    (∫ x, fourier h x ∂(haar : Measure Circle₁)) = if h = 0 then 1 else 0 := by
  have ho := (orthonormal_iff_ite.mp (@orthonormal_fourier 1 _)) 0 h
  change (∫ x, fourier h x ∂(AddCircle.haarAddCircle : Measure Circle₁)) = _
  rw [ContinuousMap.inner_toLp] at ho
  simpa only [fourier_zero, map_one, mul_one, eq_comm (a := (0 : ℤ))] using ho

private theorem tendsto_integral_fourier
    (hc : ∀ h : ℤ, h ≠ 0 → Tendsto (average h) atTop (𝓝 0)) (h : ℤ) :
    Tendsto (fun N => ∫ x, fourier h x ∂(empirical N : Measure Circle₁)) atTop
      (𝓝 (∫ x, fourier h x ∂(haar : Measure Circle₁))) := by
  rw [integral_fourier_haar]
  by_cases hh : h = 0
  · subst h
    simp
  · have he (n : ℕ) : fourier h (circlePoint n) = character h n := by
      rw [circlePoint, fourier_coe_apply]
      unfold character
      congr 1
      push_cast
      ring
    simp_rw [integral_empirical (fourier h), he, ite_eq_right hh]
    change Tendsto (fun N => average h (N + 1)) atTop (𝓝 0)
    exact (hc h hh).comp (tendsto_add_atTop_nat 1)

private theorem empirical_tendsto_haar
    (hc : ∀ h : ℤ, h ≠ 0 → Tendsto (average h) atTop (𝓝 0)) :
    Tendsto empirical atTop (𝓝 haar) := by
  let L (N : ℕ) (f : C(Circle₁, ℂ)) := ∫ x, f x ∂(empirical N : Measure Circle₁)
  let I (f : C(Circle₁, ℂ)) := ∫ x, f x ∂(haar : Measure Circle₁)
  have hLip (μ : ProbabilityMeasure Circle₁) :
      LipschitzWith 1 (fun f : C(Circle₁, ℂ) => ∫ x, f x ∂(μ : Measure Circle₁)) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul, ← integral_sub]
    · simpa using (norm_integral_le_of_norm_le_const (μ := (μ : Measure Circle₁))
        (ae_of_all _ fun x => ContinuousMap.norm_coe_le_norm (f - g) x))
    · exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hEqui : Equicontinuous L := by
    intro f
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, fun g hg N => ?_⟩
    exact ((hLip (empirical N)).dist_le_mul f g).trans_lt (by simpa [dist_comm f g] using hg)
  have hClosed : IsClosed {f : C(Circle₁, ℂ) | Tendsto (L · f) atTop (𝓝 (I f))} :=
    hEqui.isClosed_setOfPred_tendsto (hLip haar).continuous
  let S : Submodule ℂ C(Circle₁, ℂ) :=
    { carrier := {f | Tendsto (L · f) atTop (𝓝 (I f))}
      zero_mem' := by simp [L, I]
      add_mem' := by
        intro f g hf hg
        have hi (μ : ProbabilityMeasure Circle₁) (u : C(Circle₁, ℂ)) :
            Integrable u (μ : Measure Circle₁) :=
          u.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        change Tendsto (L · (f + g)) atTop (𝓝 (I (f + g)))
        simpa only [L, I, ContinuousMap.add_apply, integral_add (hi _ _) (hi _ _)] using
          (show Tendsto (L · f) atTop (𝓝 (I f)) from hf).add
            (show Tendsto (L · g) atTop (𝓝 (I g)) from hg)
      smul_mem' := by
        intro c f hf
        change Tendsto (L · (c • f)) atTop (𝓝 (I (c • f)))
        simpa only [L, I, ContinuousMap.smul_apply, integral_smul] using
          (show Tendsto (L · f) atTop (𝓝 (I f)) from hf).const_smul c }
  have hSpan : Submodule.span ℂ (range (@fourier 1)) ≤ S := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨h, rfl⟩
    exact tendsto_integral_fourier hc h
  have hAll : ∀ f : C(Circle₁, ℂ), Tendsto (L · f) atTop (𝓝 (I f)) := by
    intro f
    apply (closure_minimal hSpan hClosed)
    change f ∈ (Submodule.span ℂ (range (@fourier 1))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  refine (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr fun f => ?_
  exact hAll ⟨f, f.continuous⟩

private noncomputable def circleCell (a b : ℝ) : Set Circle₁ :=
  {x | (AddCircle.equivIco 1 0 x : ℝ) ∈ Ico a b}

private theorem preimage_cell (a b x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    (x : Circle₁) ∈ circleCell a b ↔ x ∈ Ico a b := by
  have hx' : x ∈ Ico (0 : ℝ) (0 + 1) := by simpa using hx
  change (AddCircle.equivIco 1 0 (x : Circle₁) : ℝ) ∈ Ico a b ↔ _
  rw [AddCircle.equivIco_coe_of_mem hx']

private theorem haar_cell {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    (haar : Measure Circle₁) (circleCell a b) = ENNReal.ofReal (b - a) := by
  have hm : MeasurableSet (circleCell a b) :=
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable) measurableSet_Ico
  have hv : (haar : Measure Circle₁) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp [haar]
  have hp := AddCircle.add_projection_respects_measure 1 0 hm
  simp only [zero_add] at hp
  rw [hv, hp]
  have he : ((↑) : ℝ → Circle₁) ⁻¹' circleCell a b ∩ Ico 0 1 = Ico a b := by
    ext x
    constructor
    · rintro ⟨hx, hx'⟩
      exact (preimage_cell a b x hx').mp hx
    · intro hx
      have hx' : x ∈ Ico (0 : ℝ) 1 := ⟨ha.trans hx.1, hx.2.trans_le hb⟩
      exact ⟨(preimage_cell a b x hx').mpr hx, hx'⟩
  rw [← measure_congr (Filter.EventuallyEqSet.inter (Filter.EventuallyEq.rfl)
    (Ico_ae_eq_Ioc (μ := (volume : Measure ℝ)) (a := 0) (b := 1))), he, Real.volume_Ico]

private theorem frontier_cell {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    frontier (circleCell a b) ⊆ ({(a : Circle₁), (b : Circle₁)} : Set Circle₁) := by
  let q : ℝ → Circle₁ := (↑)
  have hclosed : IsClosed (q '' Icc a b) :=
    (isCompact_Icc.image (AddCircle.continuous_mk' (1 : ℝ))).isClosed
  have hopen : IsOpen (q '' Ioo a b) := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hs₁ : circleCell a b ⊆ q '' Icc a b := by
    intro x hx
    exact ⟨AddCircle.equivIco 1 0 x, Ico_subset_Icc_self hx, AddCircle.coe_equivIco⟩
  have hs₂ : q '' Ioo a b ⊆ circleCell a b := by
    rintro _ ⟨x, hx, rfl⟩
    exact (preimage_cell a b x ⟨ha.trans hx.1.le, hx.2.trans_le hb⟩).mpr ⟨hx.1.le, hx.2⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (closure_minimal hs₁ hclosed) hx.1
  by_cases hya : y = a
  · simp [q, hya]
  by_cases hyb : y = b
  · simp [q, hyb]
  exact False.elim (hx.2 ((interior_maximal hs₂ hopen)
    ⟨y, ⟨lt_of_le_of_ne hy.1 (Ne.symm hya), lt_of_le_of_ne hy.2 hyb⟩, rfl⟩))

private theorem empirical_cell (a b : ℝ) (N : ℕ) :
    (empirical N : Measure Circle₁) (circleCell a b) =
      (↑(N + 1) : ℝ≥0∞)⁻¹ *
        ↑((List.range (N + 1)).countP (fun n => decide (point n ∈ Ico a b))) := by
  classical
  have hm : MeasurableSet (circleCell a b) :=
    (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable) measurableSet_Ico
  have he (n : ℕ) : circlePoint n ∈ circleCell a b ↔ point n ∈ Ico a b := by
    change (AddCircle.equivIco 1 0 (circlePoint n) : ℝ) ∈ Ico a b ↔ _
    have hx : (AddCircle.equivIco 1 0 (circlePoint n) : ℝ) = point n := by
      unfold circlePoint point
      rw [AddCircle.coe_equivIco_mk_apply]
      simp
    rw [hx]
  change ((↑(N + 1) : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range (N + 1),
    Measure.dirac (circlePoint n)) (circleCell a b) = _
  rw [Measure.smul_apply, Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply' _ hm, Set.indicator_apply, he, Pi.one_apply, smul_eq_mul]
  congr 1
  have hcard := (List.nodup_range (n := N + 1)).card_eq_countP
    (P := fun n => point n ∈ Ico a b)
  rw [List.toFinset_range] at hcard
  rw [← hcard, Finset.card_filter]
  push_cast
  rfl

private theorem tendsto_cell_frequency (h : Tendsto empirical atTop (𝓝 haar))
    (k j : ℕ) (hj : j < 2 ^ k) :
    Tendsto (fun N => (cellCount k j (N + 1) : ℝ) / (↑(N + 1) : ℝ)) atTop
      (𝓝 (1 / (2 : ℝ) ^ k)) := by
  let a : ℝ := (j : ℝ) / 2 ^ k
  let b : ℝ := ((j : ℝ) + 1) / 2 ^ k
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : (0 : ℝ) < 2 ^ k := by positivity
  have hb : b ≤ 1 := by
    dsimp [b]
    have hj' : (↑(j + 1) : ℝ) ≤ (↑(2 ^ k : ℕ) : ℝ) :=
      Nat.cast_le.mpr (Nat.succ_le_of_lt hj)
    simpa [div_le_iff₀ hB] using hj'
  have hw : 0 ≤ b - a := by dsimp [a, b]; rw [← sub_div, add_sub_cancel_left]; positivity
  have hnull : (haar : Measure Circle₁) (frontier (circleCell a b)) = 0 :=
    measure_mono_null (frontier_cell ha hb) (by
      have hv : (haar : Measure Circle₁) = volume := by
        rw [AddCircle.volume_eq_smul_haarAddCircle]
        simp [haar]
      rw [hv, ← singleton_union]
      have hs (x : Circle₁) : (volume : Measure Circle₁) {x} = 0 := by
        have hb := AddCircle.volume_closedBall (T := 1) (x := x) 0
        simpa using hb
      exact measure_union_null (hs _) (hs _))
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h hnull
  rw [haar_cell ha hb] at ht
  have hr := (ENNReal.tendsto_toReal (ENNReal.ofReal_ne_top : ENNReal.ofReal (b - a) ≠ ⊤)).comp ht
  change Tendsto (fun N => ((empirical N : Measure Circle₁) (circleCell a b)).toReal) atTop
    (𝓝 (ENNReal.ofReal (b - a)).toReal) at hr
  simp_rw [empirical_cell, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast] at hr
  rw [ENNReal.toReal_ofReal hw] at hr
  have he : b - a = 1 / (2 : ℝ) ^ k := by dsimp [a, b]; rw [← sub_div, add_sub_cancel_left]
  rw [he] at hr
  simpa only [a, b, cellCount, mem_Ico, div_eq_mul_inv, mul_comm] using hr

/-- Odd-mode cancellation suffices for the exact binary normality target. -/
theorem normalInBase_of_odd_mode_cancellation
    (hc : ∀ h : ℤ, h % 2 = 1 → Tendsto (average h) atTop (𝓝 0)) : NormalInBase 2 := by
  rw [normalInBase_iff_dyadic_cells]
  intro k _ j hj T hT
  have hf := tendsto_cell_frequency (empirical_tendsto_haar
    (all_nonzero_modes_iff_odd_modes.mpr hc)) k j hj
  have hB : (0 : ℝ) < 2 ^ k := by positivity
  have ht : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hr := (Metric.tendsto_atTop.mp hf) (1 / ((2 : ℝ) ^ k * T)) (by positivity)
  obtain ⟨M, hM⟩ := hr
  refine ⟨M + 1, by omega, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  have hn : M ≤ n := by omega
  have hnp : (0 : ℝ) < (↑(n + 1) : ℝ) := by positivity
  have hd := hM n hn
  rw [Real.dist_eq] at hd
  have he : ((2 : ℝ) ^ k * (cellCount k j (n + 1) : ℝ) - (↑(n + 1) : ℝ)) =
      ((cellCount k j (n + 1) : ℝ) / (↑(n + 1) : ℝ) - 1 / (2 : ℝ) ^ k) *
        ((2 : ℝ) ^ k * (↑(n + 1) : ℝ)) := by
    field_simp
  have hs : |(2 : ℝ) ^ k * (cellCount k j (n + 1) : ℝ) - (↑(n + 1) : ℝ)| * (T : ℝ) <
      (↑(n + 1) : ℝ) := by
    rw [he, abs_mul, abs_of_pos (mul_pos hB hnp)]
    have hh := (lt_div_iff₀ (mul_pos hB ht)).mp hd
    nlinarith only [mul_lt_mul_of_pos_right hh hnp]
  have hdist (x y : ℕ) : (Nat.dist x y : ℝ) = |(x : ℝ) - (y : ℝ)| := by
    rcases le_total x y with h | h
    · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
        abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  exact_mod_cast (show (Nat.dist (2 ^ k * cellCount k j (n + 1)) (n + 1) : ℝ) * (T : ℝ) ≤
    (↑(n + 1) : ℝ) by
    rw [hdist, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact hs.le)

end GoldenNormality.BinaryDyadicOrbit
