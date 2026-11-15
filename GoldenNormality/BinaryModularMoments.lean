import GoldenNormality.BinaryRationalOrbit

/-! Complete-frequency averages and a first-frequency counterexample. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators ComplexConjugate Topology
open Complex Filter

private theorem character_orthog (q : ℕ) [NeZero q] (a b : ZMod q) :
    (∑ h : ZMod q, ZMod.stdAddChar (h * a) *
      conj (ZMod.stdAddChar (h * b))) = if a = b then q else 0 := by
  have hc (x : ZMod q) :
      conj (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
    rw [AddChar.map_neg_eq_inv]
    apply (Complex.inv_eq_conj _).symm
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  simp_rw [hc, ← AddChar.map_add_eq_mul, ← mul_neg, ← mul_add, ← sub_eq_add_neg]
  have hq := AddChar.sum_mulShift (a - b) (ZMod.isPrimitive_stdAddChar q)
  simpa only [sub_eq_zero, ZMod.card, Nat.cast_ofNat] using hq

/-- Averaging over all modes measures only the collisions of the residues. -/
theorem sum_sq_modular_modes (q N : ℕ) [NeZero q] (a : ℕ → ZMod q) :
    (∑ h : ZMod q, ‖∑ i ∈ Finset.range N, ZMod.stdAddChar (h * a i)‖ ^ 2) =
      (q : ℝ) * ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if a i = a j then 1 else 0 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [character_orthog q (a i) (a j)]
  split <;> simp_all

/-- For an odd numerator, the powers of two have distinct images before the
first zero modulo (2^N). -/
theorem odd_dyadic_residues_injOn (p N : ℕ) (hp : Odd p) :
    (Set.Iio N).InjOn (fun i : ℕ => (p : ZMod (2 ^ N)) * 2 ^ i) := by
  have hc : p.Coprime (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr
      (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hp))
  let u := ZMod.unitOfCoprime p hc
  have hv : (u : ZMod (2 ^ N)) = p := rfl
  suffices h : (Set.Iio N).InjOn (fun i : ℕ => (2 : ZMod (2 ^ N)) ^ i) by
    intro i hi j hj he
    apply h hi hj
    rw [← hv] at he
    exact (Units.mul_right_inj u).mp he
  intro i hi j hj he
  have hi' : i < N := hi
  have hj' : j < N := hj
  have hi2 : (2 : ℕ) ^ i < (2 : ℕ) ^ N := pow_lt_pow_right₀ (by decide) hi'
  have hj2 : (2 : ℕ) ^ j < (2 : ℕ) ^ N := pow_lt_pow_right₀ (by decide) hj'
  have he' : ((2 ^ i : ℕ) : ZMod (2 ^ N)) = ((2 ^ j : ℕ) : ZMod (2 ^ N)) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using he
  have hv := congrArg (fun z : ZMod (2 ^ N) => z.val) he'
  rw [ZMod.val_natCast_of_lt hi2, ZMod.val_natCast_of_lt hj2] at hv
  exact (pow_right_injective₀ (by decide : 0 < (2 : ℕ)) (by decide)) hv

/-- Exact complete-frequency second moment for an odd dyadic numerator. -/
theorem sum_sq_odd_dyadic_modes (p N : ℕ) (hp : Odd p) :
    (∑ h : ZMod (2 ^ N), ‖∑ i ∈ Finset.range N,
      ZMod.stdAddChar (h * ((p : ZMod (2 ^ N)) * 2 ^ i))‖ ^ 2) =
      (2 : ℝ) ^ N * N := by
  have : NeZero (2 ^ N : ℕ) := ⟨by positivity⟩
  rw [sum_sq_modular_modes]
  push_cast
  congr 1
  have hinj := odd_dyadic_residues_injOn p N hp
  calc
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if i = j then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hi' := Finset.mem_range.mp hi
      have hj' := Finset.mem_range.mp hj
      have hiff : ((p : ZMod (2 ^ N)) * 2 ^ i) = ((p : ZMod (2 ^ N)) * 2 ^ j) ↔ i = j :=
        ⟨hinj hi' hj', fun he => by rw [he]⟩
      simp only [hiff]
    _ = _ := by simp [Finset.filter_true_of_mem]

/-- Permuting frequency labels preserves the complete spectrum as a multiset.
This equality does not track a fixed frequency. -/
theorem sum_modes_apply_odd_numerator (p N : ℕ) (hp : Odd p) (F : ℂ → ℝ) :
    (∑ h : ZMod (2 ^ N), F (∑ i ∈ Finset.range N,
      ZMod.stdAddChar (h * ((p : ZMod (2 ^ N)) * 2 ^ i)))) =
      ∑ h : ZMod (2 ^ N), F (∑ i ∈ Finset.range N,
        ZMod.stdAddChar (h * (2 : ZMod (2 ^ N)) ^ i)) := by
  have hc : p.Coprime (2 ^ N) := by
    apply Nat.Coprime.pow_right
    exact Nat.Coprime.symm (Nat.prime_two.coprime_iff_not_dvd.mpr
      (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr hp))
  let u := ZMod.unitOfCoprime p hc
  apply Fintype.sum_equiv (Units.mulRight u)
  intro h
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change ZMod.stdAddChar (h * ((p : ZMod (2 ^ N)) * 2 ^ i)) =
    ZMod.stdAddChar ((h * (u : ZMod (2 ^ N))) * 2 ^ i)
  rw [show (u : ZMod (2 ^ N)) = p by rfl, mul_assoc]

/-- The second moment is exactly the same at every actual odd floor. -/
theorem actual_odd_floor_complete_second_moment (N : ℕ)
    (hp : Odd (scaledFloor 2 N).natAbs) :
    (∑ h : ZMod (2 ^ N), ‖∑ i ∈ Finset.range N,
      ZMod.stdAddChar (h * ((scaledFloor 2 N : ZMod (2 ^ N)) * 2 ^ i))‖ ^ 2) =
      (2 : ℝ) ^ N * N := by
  have hn : 0 ≤ scaledFloor 2 N := by
    unfold scaledFloor
    exact Int.floor_nonneg.mpr (mul_nonneg (by positivity) alpha_pos.le)
  have hc : ((scaledFloor 2 N).natAbs : ℤ) = scaledFloor 2 N := Int.natAbs_of_nonneg hn
  have hz := sum_sq_odd_dyadic_modes (scaledFloor 2 N).natAbs N hp
  have he : ((scaledFloor 2 N).natAbs : ZMod (2 ^ N)) =
      (scaledFloor 2 N : ZMod (2 ^ N)) := by rw [← Int.cast_natCast, hc]
  simpa only [he] using hz

/-- At the varying rational seed `1 / 2^N`, the first mode stays close
to the first mode at zero. -/
theorem seed_one_far_from_cancellation (N : ℕ) :
    ‖averageAt (1 / (2 : ℝ) ^ N) 1 N -
      averageAt 0 1 N‖ ≤ 2 * Real.pi / (N : ℝ) := by
  have h := GoldenNormality.BinaryDyadicOrbit.norm_averageAt_sub_le
    (1 / (2 : ℝ) ^ N) 0 1 N
  simp only [Int.cast_one, abs_one, mul_one, sub_zero] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N))
  have hB : (0 : ℝ) < 2 ^ N := by positivity
  rw [mul_assoc, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 : ℝ) ^ N)]
  apply mul_le_of_le_one_right (by positivity)
  rw [mul_one_div, div_le_one hB]
  linarith

theorem seed_one_average_tends_to_one :
    Tendsto (fun N : ℕ => averageAt
      (1 / (2 : ℝ) ^ N) 1 N) atTop (𝓝 1) := by
  let f := fun N : ℕ => averageAt (1 / (2 : ℝ) ^ N) 1 N
  let g := averageAt 0 1
  have hzero : Tendsto (fun N => f N - g N) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi))
      (fun _ => norm_nonneg _) seed_one_far_from_cancellation
  have hg : Tendsto g atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hcast : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    change (1 : ℂ) = averageAt 0 1 N
    unfold averageAt
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
    exact (div_self hcast).symm
  have ht := hzero.add hg
  have he : (fun N => f N - g N + g N) = f := by funext N; ring
  rwa [he, zero_add] at ht

end GoldenNormality.BinaryDyadicOrbit
