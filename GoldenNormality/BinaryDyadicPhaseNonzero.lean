import GoldenNormality.BinaryRationalOrbit
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-! An exact finite nonvanishing condition for dyadic phase sums. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Polynomial
open Polynomial

/-- A primitive root of order (2^{k+1}), with (k>0), contributes a
nonzero power sum even after adjoining any rational constant. -/
theorem primitive_dyadic_power_sum_ne (k : ℕ) (hk : 0 < k) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) (c : ℚ) :
    (∑ i ∈ Finset.range (k + 1), ζ ^ (2 ^ i : ℕ)) + (c : ℂ) ≠ 0 := by
  have hcy : cyclotomic (2 ^ (k + 1)) ℚ = X ^ (2 ^ k : ℕ) + 1 := by
    rw [cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (n := k) Nat.prime_two]
    simp [Finset.sum_range_succ, add_comm]
  have hmin := cyclotomic_eq_minpoly_rat hζ (by positivity)
  have hroot := minpoly.aeval ℚ ζ
  rw [← hmin, hcy, map_add, map_pow, aeval_X, map_one] at hroot
  have htop : ζ ^ (2 ^ k : ℕ) = -1 := by linear_combination hroot
  let P : ℚ[X] := (∑ i ∈ Finset.range k, (X : ℚ[X]) ^ (2 ^ i : ℕ)) + C (c - 1)
  have hdeg : P.natDegree < (2 : ℕ) ^ k := by
    refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · calc
        _ ≤ 2 ^ (k - 1) := by
          apply natDegree_sum_le_of_forall_le
          intro i hi
          rw [natDegree_X_pow]
          have hi' := Finset.mem_range.mp hi
          exact pow_le_pow_right₀ (by decide) (by omega)
        _ < 2 ^ k := pow_lt_pow_right₀ (by decide) (by omega)
    · rw [natDegree_C]
      positivity
  have hp : P.coeff 1 = 1 := by
    simp only [P, coeff_add, finsetSum_coeff, coeff_X_pow, coeff_C, Nat.one_ne_zero,
      ite_false, add_zero]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro i _ hi
      have hi' : (1 : ℕ) < 2 ^ i := one_lt_pow₀ (by decide) hi
      simp [hi'.ne]
    · simp [hk]
  intro hz
  have ha : aeval ζ P = 0 := by
    rw [Finset.sum_range_succ, htop] at hz
    simpa [P, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
  have hd := natDegree_le_of_dvd (minpoly.dvd ℚ ζ ha) (show P ≠ 0 by
    intro h
    rw [h, coeff_zero] at hp
    norm_num at hp)
  rw [← hmin, natDegree_cyclotomic, Nat.totient_prime_pow_succ Nat.prime_two] at hd
  simp only [Nat.reduceSub, mul_one] at hd
  exact (not_le_of_gt hdeg) hd

private theorem power_sum_tail (ζ : ℂ) (N M : ℕ) (hM : M ≤ N)
    (hz : ζ ^ (2 ^ M : ℕ) = 1) :
    (∑ i ∈ Finset.range N, ζ ^ (2 ^ i : ℕ)) =
      (∑ i ∈ Finset.range M, ζ ^ (2 ^ i : ℕ)) + ((N - M : ℕ) : ℂ) := by
  have he : M + (N - M) = N := Nat.add_sub_of_le hM
  conv_lhs => rw [← he, Finset.sum_range_add]
  congr 1
  have h1 (i : ℕ) : ζ ^ (2 ^ (M + i) : ℕ) = 1 := by
    rw [pow_add, pow_mul, hz, one_pow]
  simp only [h1, Finset.sum_const, Finset.card_range, nsmul_one]

/-- A dyadic phase sum with at least three terms cannot vanish. This holds
for every numerator and therefore includes the actual quadratic floor. -/
theorem dyadic_phase_sum_ne_zero (N : ℕ) (hN : 3 ≤ N) (p : ZMod (2 ^ N)) :
    (∑ i ∈ Finset.range N, ZMod.stdAddChar (p * (2 : ZMod (2 ^ N)) ^ i)) ≠ 0 := by
  have : NeZero (2 ^ N : ℕ) := ⟨by positivity⟩
  let ζ := ZMod.stdAddChar p
  have he (i : ℕ) : ZMod.stdAddChar (p * (2 : ZMod (2 ^ N)) ^ i) = ζ ^ (2 ^ i : ℕ) := by
    change ZMod.stdAddChar (p * (2 : ZMod (2 ^ N)) ^ i) =
      ZMod.stdAddChar p ^ (2 ^ i : ℕ)
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, mul_comm]
  simp_rw [he]
  have hz : ζ ^ (2 ^ N : ℕ) = 1 := by
    change ZMod.stdAddChar p ^ (2 ^ N : ℕ) = 1
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
      AddChar.map_zero_eq_one]
  obtain ⟨M, hMn, horder⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hz)
  have hpow : IsPrimitiveRoot ζ (2 ^ M) := horder ▸ IsPrimitiveRoot.orderOf ζ
  by_cases hm0 : M = 0
  · have hζ : ζ = 1 := by simpa only [hm0, pow_zero, pow_one] using hpow.pow_eq_one
    simp [hζ, (show N ≠ 0 by omega)]
  rw [power_sum_tail _ _ _ hMn hpow.pow_eq_one]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  by_cases hm' : m = 0
  · have h2 : M = 1 := by omega
    have hζm : ζ = -1 := by
      apply IsPrimitiveRoot.eq_neg_one_of_two_right
      simpa only [h2, pow_one] using hpow
    rw [h2, Finset.sum_range_one, pow_zero, pow_one, hζm]
    intro hz
    have hr := congrArg Complex.re hz
    have hn1 : (2 : ℝ) ≤ (↑(N - 1) : ℝ) := by exact_mod_cast (show 2 ≤ N - 1 by omega)
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.natCast_re,
      Complex.zero_re] at hr
    linarith only [hr, hn1]
  · have hmpos := Nat.pos_of_ne_zero hm'
    have hp' : IsPrimitiveRoot ζ (2 ^ (m + 1)) := by simpa only [hm, Nat.succ_eq_add_one] using hpow
    have hsum := primitive_dyadic_power_sum_ne m hmpos ζ hp' (↑(N - M) : ℚ)
    simpa only [← Nat.succ_eq_add_one, ← hm, Rat.cast_natCast] using hsum

/-- The exact normalized modular average of an actual binary prefix cannot
be zero once the prefix contains at least three digits. -/
theorem dyadicModularAverage_ne_zero (h : ℤ) (N : ℕ) (hN : 3 ≤ N) :
    dyadicModularAverage h N ≠ 0 := by
  have : NeZero (2 ^ N : ℕ) := ⟨by positivity⟩
  have hsum := dyadic_phase_sum_ne_zero N hN
    ((h : ZMod (2 ^ N)) * (scaledFloor 2 N : ZMod (2 ^ N)))
  unfold dyadicModularAverage
  exact div_ne_zero hsum (by exact_mod_cast (show N ≠ 0 by omega))

/-- The actual two-digit prefix gives exact cancellation at frequency one. -/
theorem dyadicModularAverage_one_two : dyadicModularAverage 1 2 = 0 := by
  have hf : scaledFloor 2 2 = 2 := by
    unfold scaledFloor
    rw [show ((2 : ℕ) : ℝ) ^ 2 = 4 by norm_num]
    exact (prefixCertificate_iff_intFloor (B := 4) (q := 2) (by decide)).mp (by decide)
  let χ : AddChar (ZMod 4) ℂ := ZMod.stdAddChar
  have hpow : χ 2 ^ 2 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show (2 : ℕ) • (2 : ZMod 4) = 0 by decide,
      AddChar.map_zero_eq_one]
  have hneq : χ 2 ≠ 1 := by
    rw [← χ.map_zero_eq_one]
    exact fun h => (by decide : (2 : ZMod 4) ≠ 0) (ZMod.injective_stdAddChar h)
  have hχ : χ 2 = -1 := (sq_eq_one_iff.mp hpow).resolve_left hneq
  change (∑ n ∈ Finset.range (1 + 1), χ ((scaledFloor 2 2 : ZMod 4) * 2 ^ n)) /
    (2 : ℂ) = 0
  rw [hf, Finset.sum_range_succ, Finset.sum_range_one]
  change (χ (2 * 1) + χ (2 * 2)) / (2 : ℂ) = 0
  rw [mul_one, show (2 : ZMod 4) * 2 = 0 by decide, hχ, AddChar.map_zero_eq_one]
  simp

end GoldenNormality.BinaryDyadicOrbit
