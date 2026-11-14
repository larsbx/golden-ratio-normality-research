import GoldenNormality.BinaryDyadicOrbit
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-! Exact rational controls for finite-frequency normality tests. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Topology
open Filter Set

private theorem order_two (k : ℕ) :
    orderOf (2 : ZMod (3 ^ (k + 1))) = 2 * 3 ^ k := by
  have h3 : Nat.Prime 3 := by decide
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h4 : orderOf ((2 : ZMod (3 ^ (k + 1))) ^ 2) = 3 ^ k := by
    simpa only [show (2 : ZMod (3 ^ (k + 1))) ^ 2 = 1 + 3 by ring, Nat.cast_ofNat] using
      ZMod.orderOf_one_add_prime h3 (by decide) k
  let m := orderOf (2 : ZMod (3 ^ (k + 1)))
  have hdiv : m / Nat.gcd m 2 = 3 ^ k := by
    rwa [orderOf_pow' _ (by decide : (2 : ℕ) ≠ 0)] at h4
  have heven : 2 ∣ m := by
    have hx : (2 : ZMod (3 ^ (k + 1))) ^ m = 1 := pow_orderOf_eq_one _
    let f : ZMod (3 ^ (k + 1)) →+* ZMod 3 := ZMod.castHom (dvd_pow_self 3 (by omega)) _
    have hy := congrArg f hx
    simp only [map_pow, map_ofNat, map_one] at hy
    apply orderOf_dvd_iff_pow_eq_one.mpr at hy
    have ho : orderOf (2 : ZMod 3) = 2 := by
      apply orderOf_eq_prime
      · decide
      · decide
    rwa [ho] at hy
  rw [Nat.gcd_eq_right heven] at hdiv
  rw [← hdiv, mul_comm, Nat.div_mul_cancel heven]

private theorem units_enum (k : ℕ) :
    Function.Bijective (fun n : Fin (2 * 3 ^ k) =>
      (ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by decide).pow_right (k + 1))) ^ (n : ℕ)) := by
  let p := 3 ^ (k + 1)
  have : NeZero p := ⟨by dsimp [p]; positivity⟩
  let u : (ZMod p)ˣ := ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by decide).pow_right _)
  change Function.Bijective (fun n : Fin (2 * 3 ^ k) => u ^ (n : ℕ))
  have ho : orderOf u = 2 * 3 ^ k := by
    rw [← orderOf_units]
    dsimp only [u]
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
    exact order_two k
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro a b h
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (show a.val < orderOf u by rw [ho]; exact a.isLt)
      (show b.val < orderOf u by rw [ho]; exact b.isLt) h
  · rw [Fintype.card_fin, ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)]
    omega

private noncomputable def controlPhase (k : ℕ) (h : ℤ) (n : ℕ) : ℂ :=
  letI : NeZero (3 ^ (k + 1) : ℕ) := ⟨by positivity⟩
  ZMod.stdAddChar ((h : ZMod (3 ^ (k + 1))) * (2 : ZMod (3 ^ (k + 1))) ^ n)

private theorem controlPhase_period (k : ℕ) (h : ℤ) :
    Function.Periodic (controlPhase k h) (2 * 3 ^ k) := by
  intro n
  have hpow : (2 : ZMod (3 ^ (k + 1))) ^ (2 * 3 ^ k) = 1 := by
    rw [← order_two k]
    exact pow_orderOf_eq_one _
  simp only [controlPhase, pow_add, hpow, mul_one]

private theorem controlPhase_norm (k : ℕ) (h : ℤ) (n : ℕ) :
    ‖controlPhase k h n‖ = 1 := by
  unfold controlPhase
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem controlPhase_real (k : ℕ) (h : ℤ) (n : ℕ) :
    controlPhase k h n =
      Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (2 : ℂ) ^ n /
        (↑(3 ^ (k + 1) : ℕ) : ℂ)) := by
  unfold controlPhase
  rw [← Int.cast_ofNat, ← Int.cast_pow, ← Int.cast_mul, ZMod.stdAddChar_coe]
  push_cast
  ring_nf

private theorem period_sum_zero (k : ℕ) (h : ℤ)
    (hn : (h : ZMod (3 ^ k)) ≠ 0) :
    ∑ n ∈ Finset.range (2 * 3 ^ k), controlPhase k h n = 0 := by
  let q := 3 ^ k
  let p := 3 ^ (k + 1)
  have hqp : p = 3 * q := by dsimp [p, q]; rw [pow_succ, mul_comm]
  have : NeZero q := ⟨by dsimp [q]; positivity⟩
  have : NeZero p := ⟨by dsimp [p]; positivity⟩
  let char := fun x : ZMod p => ZMod.stdAddChar (x * (h : ZMod p))
  have hp : (h : ZMod p) ≠ 0 := by
    intro hz
    let f : ZMod p →+* ZMod q := ZMod.castHom (by rw [hqp]; exact dvd_mul_left q 3) _
    have hz' := congrArg f hz
    exact hn (by simpa only [map_intCast, map_zero] using hz')
  have hall : ∑ x : ZMod p, char x = 0 := by
    simpa only [ite_eq_right hp, Nat.cast_zero] using
      AddChar.sum_mulShift (h : ZMod p) (ZMod.isPrimitive_stdAddChar p)
  have en := units_enum k
  let equ : Fin (2 * 3 ^ k) ≃ (ZMod p)ˣ := Equiv.ofBijective _ en
  have hsum : (∑ n ∈ Finset.range (2 * 3 ^ k), controlPhase k h n) =
      ∑ u : (ZMod p)ˣ, char u := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Fintype.sum_equiv equ
    intro i
    change controlPhase k h i = char ((ZMod.unitOfCoprime 2
      ((show Nat.Coprime 2 3 by decide).pow_right (k + 1)) : (ZMod p)ˣ) ^ (i : ℕ))
    simp only [char, controlPhase, ZMod.coe_unitOfCoprime,
      Nat.cast_ofNat, mul_comm]
  rw [hsum]
  let nonunits := {x : ZMod p // ¬IsUnit x}
  let eqU : (ZMod p)ˣ ≃ {x : ZMod p // IsUnit x} :=
    ⟨fun u => ⟨u, u.isUnit⟩, fun x => x.property.unit,
      fun u => Units.ext (IsUnit.unit_spec u.isUnit), fun x => Subtype.ext x.property.unit_spec⟩
  have hu : (∑ u : (ZMod p)ˣ, char u) = ∑ u : {x : ZMod p // IsUnit x}, char u :=
    Fintype.sum_equiv eqU _ _ (fun _ => rfl)
  rw [hu]
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun x : ZMod p => IsUnit x) char
  rw [hall] at hpart
  suffices hnon : ∑ x : nonunits, char x = 0 by
    change (∑ x : {x : ZMod p // IsUnit x}, char x) + (∑ x : nonunits, char x) = 0 at hpart
    simpa only [hnon, add_zero] using hpart
  have hdiv (x : nonunits) : 3 ∣ (x : ZMod p).val := by
    have hx := x.property
    rw [← ZMod.natCast_zmod_val (x : ZMod p)] at hx
    exact not_not.mp (fun hnot => hx ((ZMod.isUnit_natCast_iff_not_dvd_pow
      (by decide : Nat.Prime 3) (by omega : 0 < k + 1)).mpr hnot))
  let e : ZMod q → nonunits := fun x =>
    ⟨((3 * x.val : ℕ) : ZMod p), by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (by decide : Nat.Prime 3) (by omega : 0 < k + 1)]
      exact not_not.mpr (dvd_mul_right 3 _)⟩
  have hv (x : ZMod q) : (e x : ZMod p).val = 3 * x.val := by
    apply ZMod.val_natCast_of_lt
    rw [hqp]
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) (by decide)
  have hb : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply ZMod.val_injective q
      have hh := congrArg (fun z : nonunits => (z : ZMod p).val) hxy
      simp only [hv] at hh
      omega
    · intro y
      refine ⟨((y : ZMod p).val / 3 : ℕ), ?_⟩
      apply Subtype.ext
      apply ZMod.val_injective p
      rw [hv, ZMod.val_natCast_of_lt]
      · rw [mul_comm, Nat.div_mul_cancel (hdiv y)]
      · have hy := ZMod.val_lt (y : ZMod p)
        have hy' := hy.trans_le (le_of_eq hqp)
        omega
  let eqN := Equiv.ofBijective e hb
  have eqC (x : ZMod q) : char (e x) = ZMod.stdAddChar (x * (h : ZMod q)) := by
    have hne : (q : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
    have hz : (p : ℂ) = 3 * (q : ℂ) := by exact_mod_cast hqp
    change ZMod.stdAddChar (((3 * x.val : ℕ) : ZMod p) * (h : ZMod p)) = _
    have hx : (((x.val : ℕ) : ℤ) : ZMod q) = x := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hp' : (((3 * x.val : ℕ) : ℤ) : ZMod p) = ((3 * x.val : ℕ) : ZMod p) :=
      Int.cast_natCast _
    rw [← hp', ← Int.cast_mul, ZMod.stdAddChar_coe]
    conv_rhs =>
      rw [← hx, ← Int.cast_mul, ZMod.stdAddChar_coe]
    push_cast
    rw [hz]
    congr 1
    field_simp
  have ht : (∑ x : ZMod q, ZMod.stdAddChar (x * (h : ZMod q))) =
      ∑ x : nonunits, char x := by
    exact Fintype.sum_equiv eqN _ _ (fun x => (eqC x).symm)
  rw [← ht]
  simpa only [ite_eq_right hn, Nat.cast_zero] using
    AddChar.sum_mulShift (h : ZMod q) (ZMod.isPrimitive_stdAddChar q)


private noncomputable def controlAverage (k : ℕ) (h : ℤ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, controlPhase k h n) / (N : ℂ)

private theorem control_tendsto_zero (k : ℕ) (h : ℤ)
    (hn : (h : ZMod (3 ^ k)) ≠ 0) :
    Tendsto (controlAverage k h) atTop (𝓝 0) := by
  let P : ℕ := 2 * 3 ^ k
  have hP : 0 < P := by dsimp [P]; positivity
  have hzero := period_sum_zero k h hn
  let f := controlPhase k h
  have hper : Function.Periodic f P := controlPhase_period k h
  have hshift (n q : ℕ) : f (q * P + n) = f n := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show (q + 1) * P + n = (q * P + n) + P by ring, hper, ih]
  have hblocks (q : ℕ) : ∑ n ∈ Finset.range (q * P), f n = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, zero_add]
      simpa only [hshift] using hzero
  have hbound (N : ℕ) : ‖∑ n ∈ Finset.range N, f n‖ ≤ (P : ℝ) := by
    have he := Nat.div_add_mod N P
    conv_lhs => rw [show N = N / P * P + N % P by rw [mul_comm (N / P) P, he]]
    rw [Finset.sum_range_add, hblocks, zero_add]
    simp_rw [hshift]
    calc
      _ ≤ ∑ n ∈ Finset.range (N % P), ‖f n‖ := norm_sum_le _ _
      _ = (↑(N % P) : ℝ) := by simp [f, controlPhase_norm]
      _ ≤ (P : ℝ) := by exact_mod_cast (Nat.mod_lt N hP).le
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (P : ℝ))
  · intro N
    exact norm_nonneg _
  · intro N
    change ‖(∑ n ∈ Finset.range N, f n) / (N : ℂ)‖ ≤ (P : ℝ) / (N : ℝ)
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hbound N) (Nat.cast_nonneg N)

private theorem control_invisible_mode (k : ℕ) (N : ℕ) (hN : 0 < N) :
    controlAverage k (↑(3 ^ (k + 1) : ℕ)) N = 1 := by
  have hf (n : ℕ) : controlPhase k (↑(3 ^ (k + 1) : ℕ)) n = 1 := by
    simp only [controlPhase, Int.cast_natCast, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  unfold controlAverage
  simp only [hf, Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
  exact div_self (by exact_mod_cast hN.ne')

/-- A rational binary orbit can cancel at every frequency in any fixed
bounded range while failing at a larger odd frequency. -/
theorem finite_modes_can_miss_larger_odd (H : ℕ) :
    ∃ q : ℕ, 1 < q ∧
      (∀ h : ℤ, 0 < h.natAbs → h.natAbs ≤ H →
        Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N,
          Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (2 : ℂ) ^ n / (q : ℂ))) /
            (N : ℂ)) atTop (𝓝 0)) ∧
      Odd q ∧
      (∀ N : ℕ, 0 < N → (∑ n ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * (q : ℂ) * (2 : ℂ) ^ n / (q : ℂ))) /
          (N : ℂ) = 1) := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt H (show 1 < (3 : ℕ) by decide)
  refine ⟨3 ^ (k + 1), ?_, ?_, ?_, ?_⟩
  · rw [pow_succ]
    have hpos : 0 < (3 : ℕ) ^ k := by positivity
    omega
  · intro h hpos hH
    have hn : (h : ZMod (3 ^ k)) ≠ 0 := by
      intro hz
      have hdiv : (↑(3 ^ k : ℕ) : ℤ) ∣ h := (ZMod.intCast_zmod_eq_zero_iff_dvd h _).mp hz
      have hd : 3 ^ k ∣ h.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdiv
      exact (not_le_of_gt (hH.trans_lt hk)) (Nat.le_of_dvd hpos hd)
    have hc := control_tendsto_zero k h hn
    change Tendsto (fun N => (∑ n ∈ Finset.range N, controlPhase k h n) /
      (N : ℂ)) atTop (𝓝 0) at hc
    simpa only [controlPhase_real] using hc
  · exact (show Odd (3 : ℕ) by decide).pow
  · intro N hN
    simpa only [controlAverage, controlPhase_real, Int.cast_natCast] using
      control_invisible_mode k N hN

end GoldenNormality.BinaryDyadicOrbit
