import GoldenNormality.BinaryThirdFrequency

open GoldenNormality GoldenNormality.BinaryDyadicOrbit
open scoped BigOperators

#check (thirdSource_quadratic : thirdSource ^ 2 - 7 * thirdSource + 1 = 0)

#check (thirdBranch_ge_iff_residual :
  ∀ (n : ℕ) (j : ℤ), j ≤ 2 →
    (j ≤ thirdBranch n ↔
      3 * (3 * (2 : ℤ) ^ n - 2 * BinaryComplement.scaledFloor n) * j - j ^ 2 ≤
        9 * BinaryComplement.prefixResidual n))

#check (thirdSource_residual_from_carry :
  ∀ (n : ℕ),
    let B := (2 : ℤ) ^ n
    let q := ⌊(2 : ℝ) ^ n * thirdSource⌋
    let j := thirdBranch n
    q ^ 2 - 7 * B * q + B ^ 2 =
      9 * (BinaryComplement.convolutionSuffix n - B * BinaryComplement.carry n) -
        3 * (3 * B - 2 * BinaryComplement.scaledFloor n) * j + j ^ 2)

#check (thirdSource_floor_add_branch_correction :
  ∀ (n : ℕ), ⌊(2 : ℝ) ^ n * thirdSource⌋ + (3 - thirdBranch n) =
    2 * (2 : ℤ) ^ n - 3 * scaledFloor 2 n)

#check (real_dyadicModularAverage_three_le_iff_lagTwo_energy :
  ∀ (N : ℕ), 0 < N → ∀ (ε : ℝ),
    let x := (scaledFloor 2 N : ℝ) / (2 : ℝ) ^ N
    (dyadicModularAverage 3 N).re ≤ ε ↔
      2 * (N : ℝ) * (1 - ε) ≤
        ∑ n ∈ Finset.range N, ‖phaseAt x (n + 2) - phaseAt x n‖ ^ 2)

#print axioms thirdSource_quadratic
#print axioms thirdSource_floor
#print axioms thirdBranch_ge_iff_residual
#print axioms thirdSource_residual_from_carry
#print axioms thirdSource_floor_add_branch_correction
#print axioms real_dyadicModularAverage_three_eq_lagTwo_energy
#print axioms real_dyadicModularAverage_three_le_iff_lagTwo_energy

#check (thirdTail_rational_cutoff :
  ∀ (n : ℕ) (a m : ℤ), 0 < m → a ≤ m →
    let B := (2 : ℤ) ^ n
    let r := ⌊(2 : ℝ) ^ n * thirdSource⌋
    let R := r ^ 2 - 7 * B * r + B ^ 2
    (a : ℝ) / (m : ℝ) ≤ Int.fract ((2 : ℝ) ^ n * thirdSource) ↔
      a * m * (7 * B - 2 * r) - a ^ 2 ≤ m ^ 2 * R)

#print axioms rational_cutoff_iff_quadratic
#print axioms thirdTail_rational_cutoff
