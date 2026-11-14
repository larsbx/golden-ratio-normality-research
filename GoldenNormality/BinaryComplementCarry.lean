import GoldenNormality.BinaryComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite signed carries for the actual complementary quadratic

The source throughout is `beta = 1 - alpha`. Its polynomial is
`beta^2 - 3*beta + 1 = 0`, with the negative coefficient retained.
The convolution coefficient indexed by `N` belongs to the binary place
`N + 1`; digits retain their zero-based positions.

The finite convolution prefix and suffix decompose the square of the actual
scaled floor. The suffix is an uncarried convolution and is not a Euclidean
remainder. Signed carries can be negative. These finite identities and their
conditional positivity propagation do not establish an aggregate tail bound,
a square-root lower bound on zero counts, or normality.
-/

namespace GoldenNormality.BinaryComplement

open scoped BigOperators

/-- Signed evaluation of the complementary quadratic, without natural subtraction. -/
def quadraticResidual (B q : ℤ) : ℤ := q ^ 2 - 3 * B * q + B ^ 2

/-- Exact polynomial update when one digit is appended. -/
theorem quadraticResidual_step (B q d : ℤ) :
    quadraticResidual (2 * B) (2 * q + d) =
      4 * quadraticResidual B q + 2 * d * (2 * q - 3 * B) + d ^ 2 := by
  unfold quadraticResidual
  ring

/-- The signed polynomial evaluated at the actual complementary prefix. -/
noncomputable def prefixResidual (N : ℕ) : ℤ :=
  quadraticResidual ((2 : ℤ) ^ N) (scaledFloor N)

theorem scaledFloor_succ (N : ℕ) :
    scaledFloor (N + 1) = 2 * scaledFloor N + digit N := by
  unfold digit
  ring

/-- Both residual bounds concern the actual floor, not an arbitrary integer. -/
theorem prefixResidual_bounds (N : ℕ) :
    0 < prefixResidual N ∧ prefixResidual N < 3 * (2 : ℤ) ^ N := by
  let q := wordValue 2 (BinaryAutomaton.powerDigits 0 N)
  have certificate : PrefixCertificate (2 ^ N) q := prefixCertificate_powerDigits N
  have hfloor : GoldenNormality.scaledFloor 2 N = (q : ℤ) := by
    have h := (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ N)).mp certificate
    simpa only [GoldenNormality.scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using h
  have hlo : (q : ℤ) ^ 2 + (2 : ℤ) ^ N * q < ((2 : ℤ) ^ N) ^ 2 := by
    exact_mod_cast binary_prefix_polynomial_lt certificate
  have hhi : ((2 : ℤ) ^ N) ^ 2 <
      ((q : ℤ) + 1) ^ 2 + (2 : ℤ) ^ N * ((q : ℤ) + 1) := by
    exact_mod_cast certificate.2
  have hq : (q : ℤ) < (2 : ℤ) ^ N := by
    exact_mod_cast certified_prefix_lt_scale (by positivity : 0 < 2 ^ N) certificate
  simp only [prefixResidual, quadraticResidual, scaledFloor_eq_complement, hfloor]
  constructor <;> nlinarith

/-- The exact signed residual update for the actual prefix sequence. -/
theorem prefixResidual_succ (N : ℕ) :
    prefixResidual (N + 1) = 4 * prefixResidual N +
      2 * digit N * (2 * scaledFloor N - 3 * (2 : ℤ) ^ N) + digit N ^ 2 := by
  unfold prefixResidual
  rw [pow_succ, mul_comm ((2 : ℤ) ^ N) 2, scaledFloor_succ, quadraticResidual_step]

/-- Coefficient of place `N+1` in the uncarried square of the binary expansion.
For `N=0` the empty sum is zero; for `N=1` it is `digit 0 ^ 2`. -/
noncomputable def convolutionCoefficient (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N, digit i * digit (N - 1 - i)

/-- Coefficient of place `N+1` in the nonconstant part of the signed quadratic. -/
noncomputable def signedCoefficient (N : ℕ) : ℤ :=
  convolutionCoefficient N - 3 * digit N

/-- The finite high convolution, with all digit products whose place is at most `N`.
The inner scaled floor already carries the correct binary positional weights. -/
noncomputable def convolutionPrefix (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N, digit i * scaledFloor (N - 1 - i)

/-- The remaining finite uncarried convolution, using actual suffix blocks.
It need not be smaller than the scale `2^N`. -/
noncomputable def convolutionSuffix (N : ℕ) : ℤ :=
  ∑ i ∈ Finset.range N,
    digit i * (2 : ℤ) ^ (N - 1 - i) * blockValue (N - 1 - i) (i + 1)

/-- Exact weighted reconstruction of the actual scaled floor from its digits. -/
theorem scaledFloor_eq_digit_sum (N : ℕ) :
    scaledFloor N = ∑ i ∈ Finset.range N, digit i * (2 : ℤ) ^ (N - 1 - i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [scaledFloor_succ, ih, Finset.sum_range_succ]
    have hs : (∑ i ∈ Finset.range N, digit i * (2 : ℤ) ^ (N + 1 - 1 - i)) =
        2 * ∑ i ∈ Finset.range N, digit i * (2 : ℤ) ^ (N - 1 - i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [show N + 1 - 1 - i = (N - 1 - i) + 1 by omega, pow_succ]
      ring
    rw [hs]
    simp

theorem convolutionCoefficient_nonneg (N : ℕ) : 0 ≤ convolutionCoefficient N := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (digit_range i).1 (digit_range (N - 1 - i)).1

theorem convolutionPrefix_nonneg (N : ℕ) : 0 ≤ convolutionPrefix N := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (digit_range i).1 (scaledFloor_nonneg (N - 1 - i))

theorem convolutionSuffix_nonneg (N : ℕ) : 0 ≤ convolutionSuffix N := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (digit_range i).1 (by positivity))
    (blockValue_nonneg (N - 1 - i) (i + 1))

/-- The high convolution advances by the next uncarried quadratic coefficient. -/
theorem convolutionPrefix_succ (N : ℕ) :
    convolutionPrefix (N + 1) =
      2 * convolutionPrefix N + convolutionCoefficient N := by
  unfold convolutionPrefix convolutionCoefficient
  rw [Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel, Nat.sub_self, scaledFloor_zero, mul_zero, add_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [show N - i = (N - 1 - i) + 1 by omega, scaledFloor_succ]
  ring

/-- Exact finite square decomposition. The suffix is nonnegative but uncarried;
calling it the ordinary remainder of the square modulo `2^N` would be incorrect. -/
theorem scaledFloor_square_decomposition (N : ℕ) :
    scaledFloor N ^ 2 =
      (2 : ℤ) ^ N * convolutionPrefix N + convolutionSuffix N := by
  calc
    scaledFloor N ^ 2 =
        ∑ i ∈ Finset.range N, digit i * (2 : ℤ) ^ (N - 1 - i) * scaledFloor N := by
      rw [← Finset.sum_mul, ← scaledFloor_eq_digit_sum]
      ring
    _ = ∑ i ∈ Finset.range N,
        ((2 : ℤ) ^ N * (digit i * scaledFloor (N - 1 - i)) +
          digit i * (2 : ℤ) ^ (N - 1 - i) * blockValue (N - 1 - i) (i + 1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have he : N - 1 - i + (i + 1) = N := by omega
      have hblock : blockValue (N - 1 - i) (i + 1) =
          scaledFloor N - (2 : ℤ) ^ (i + 1) * scaledFloor (N - 1 - i) := by
        simp only [blockValue, he]
      have hp : (2 : ℤ) ^ (N - 1 - i) * (2 : ℤ) ^ (i + 1) = (2 : ℤ) ^ N := by
        rw [← pow_add, he]
      calc
        _ = digit i * ((2 : ℤ) ^ (N - 1 - i) * (2 : ℤ) ^ (i + 1)) *
            scaledFloor (N - 1 - i) +
            digit i * (2 : ℤ) ^ (N - 1 - i) * blockValue (N - 1 - i) (i + 1) := by
          rw [hblock]
          ring
        _ = _ := by rw [hp]; ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; rfl

/-- Integer carry after the first `N` signed quadratic coefficients.
The polynomial's constant term gives `carry 0 = -1`. -/
noncomputable def carry (N : ℕ) : ℤ :=
  3 * scaledFloor N - (2 : ℤ) ^ N - convolutionPrefix N

@[simp] theorem carry_zero : carry 0 = -1 := by
  simp [carry, convolutionPrefix]

/-- The source-bound signed carry recurrence. The coefficient indexed by `N`
belongs to the step from `N` to `N+1`, not the preceding digit. -/
theorem carry_recurrence (N : ℕ) :
    2 * carry N = carry (N + 1) + signedCoefficient N := by
  simp only [carry, signedCoefficient, scaledFloor_succ, convolutionPrefix_succ, pow_succ]
  ring

/-- The exact finite tail identity, retaining both the uncarried suffix and
the signed polynomial residual of the actual prefix. -/
theorem carry_suffix_residual (N : ℕ) :
    (2 : ℤ) ^ N * carry N = convolutionSuffix N - prefixResidual N := by
  have h := scaledFloor_square_decomposition N
  unfold carry prefixResidual quadraticResidual
  nlinarith only [h]

/-- The carry is the negative of the scaled finite signed polynomial truncation.
This is a finite identity; no infinite-series convergence theorem is used. -/
theorem carry_eq_signed_sum (N : ℕ) :
    carry N = -(2 : ℤ) ^ N -
      ∑ i ∈ Finset.range N, signedCoefficient i * (2 : ℤ) ^ (N - 1 - i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs :
        (∑ i ∈ Finset.range (N + 1), signedCoefficient i * (2 : ℤ) ^ (N + 1 - 1 - i)) =
        2 * (∑ i ∈ Finset.range N, signedCoefficient i * (2 : ℤ) ^ (N - 1 - i)) +
          signedCoefficient N := by
      rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, mul_one]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [show N - i = (N - 1 - i) + 1 by omega, pow_succ]
      ring
    have hr := carry_recurrence N
    rw [ih] at hr
    rw [hs, pow_succ]
    linarith

/-- The signed carry is bounded below by `-2` at every source position.
Negative carries are retained, including the sharp value at `N=1`. -/
theorem carry_lower_bound (N : ℕ) : -2 ≤ carry N := by
  have hB : 0 < (2 : ℤ) ^ N := by positivity
  have hs := convolutionSuffix_nonneg N
  have hp := (prefixResidual_bounds N).2
  have he := carry_suffix_residual N
  by_contra hnot
  have hlow : carry N ≤ -3 := by omega
  have hm := mul_le_mul_of_nonneg_left hlow (le_of_lt hB)
  nlinarith

/-- The uncarried suffix is at most its scale times the actual prefix's one count. -/
theorem convolutionSuffix_le_digit_sum (N : ℕ) :
    convolutionSuffix N ≤ (2 : ℤ) ^ N * ∑ i ∈ Finset.range N, digit i := by
  unfold convolutionSuffix
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have he : N - 1 - i + (i + 1) = N := by omega
  have hp : (2 : ℤ) ^ (N - 1 - i) * (2 : ℤ) ^ (i + 1) = (2 : ℤ) ^ N := by
    rw [← pow_add, he]
  calc
    _ ≤ digit i * (2 : ℤ) ^ (N - 1 - i) * (2 : ℤ) ^ (i + 1) :=
      mul_le_mul_of_nonneg_left (le_of_lt (blockValue_lt (N - 1 - i) (i + 1)))
        (mul_nonneg (digit_range i).1 (by positivity))
    _ = _ := by rw [mul_assoc, hp]; ring

/-- Pointwise carry control by the actual number of complementary one digits.
An aggregate bound over many carries requires additional reasoning. -/
theorem carry_lt_digit_sum (N : ℕ) :
    carry N < ∑ i ∈ Finset.range N, digit i := by
  have hB : 0 < (2 : ℤ) ^ N := by positivity
  have hs := convolutionSuffix_le_digit_sum N
  have hp := (prefixResidual_bounds N).1
  have he := carry_suffix_residual N
  by_contra hnot
  have hle : (∑ i ∈ Finset.range N, digit i) ≤ carry N := by omega
  have hm := mul_le_mul_of_nonneg_left hle (le_of_lt hB)
  nlinarith

/-- Positivity propagates backward across a zero digit. The direction and the
zero hypothesis are essential because the signed coefficient can be negative. -/
theorem carry_positive_of_zero_step (N : ℕ) (hzero : digit N = 0)
    (hpositive : 0 < carry (N + 1)) : 0 < carry N := by
  have hr := carry_recurrence N
  have hc := convolutionCoefficient_nonneg N
  simp only [signedCoefficient, hzero, mul_zero, sub_zero] at hr
  omega

/-- Backward positivity across a source-bound interval of zero digits.
The upper endpoint is excluded from the zero-digit hypotheses. -/
theorem carry_positive_of_zero_gap (start length : ℕ)
    (zeros : ∀ i : ℕ, start ≤ i → i < start + length → digit i = 0)
    (hpositive : 0 < carry (start + length)) : 0 < carry start := by
  induction length generalizing start with
  | zero => simpa using hpositive
  | succ length ih =>
    have hzero : digit start = 0 := zeros start (le_refl _) (by omega)
    have hrest : ∀ i : ℕ, start + 1 ≤ i → i < start + 1 + length → digit i = 0 := by
      intro i hi hj
      exact zeros i (by omega) (by omega)
    have hend : 0 < carry (start + 1 + length) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hpositive
    exact carry_positive_of_zero_step start hzero (ih (start + 1) hrest hend)

/-- A positive quadratic coefficient followed by three actual zero digits
forces a positive carry at its left endpoint. Otherwise the recurrence would
force a later carry below the universal lower bound `-2`. -/
theorem carry_positive_of_convolution_three_zeroes (N : ℕ)
    (hconvolution : 0 < convolutionCoefficient N)
    (hzero : digit N = 0) (hzero1 : digit (N + 1) = 0)
    (hzero2 : digit (N + 2) = 0) : 0 < carry N := by
  have hr0 : 2 * carry N = carry (N + 1) + convolutionCoefficient N := by
    simpa only [signedCoefficient, hzero, mul_zero, sub_zero] using carry_recurrence N
  have hr1 : 2 * carry (N + 1) = carry (N + 2) + convolutionCoefficient (N + 1) := by
    simpa [signedCoefficient, hzero1, Nat.add_assoc] using carry_recurrence (N + 1)
  have hr2 : 2 * carry (N + 2) = carry (N + 3) + convolutionCoefficient (N + 2) := by
    simpa [signedCoefficient, hzero2, Nat.add_assoc] using carry_recurrence (N + 2)
  have hc1 := convolutionCoefficient_nonneg (N + 1)
  have hc2 := convolutionCoefficient_nonneg (N + 2)
  have hbound := carry_lower_bound (N + 3)
  omega

end GoldenNormality.BinaryComplement
