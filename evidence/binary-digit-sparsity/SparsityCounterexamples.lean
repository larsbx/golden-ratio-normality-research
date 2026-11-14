import GoldenNormality.BinarySparsity
namespace GoldenNormality.SparsityCounterexamples
open FiniteMathKernels BinaryAutomaton

theorem emptyCertificate : PrefixCertificate (2 ^ 0) 0 := by decide

theorem emptyBound :
    2 * 0 ≤ binaryWeight 0 ^ 2 + 3 * binaryWeight 0 + 4 :=
  binary_prefix_weight_bound emptyCertificate

theorem firstThreeCertificate : PrefixCertificate (2 ^ 3) 4 := by decide

theorem firstThreeWeight : binaryWeight 4 = 1 := by decide

theorem firstThreeBound :
    2 * 3 ≤ binaryWeight 4 ^ 2 + 3 * binaryWeight 4 + 4 :=
  binary_prefix_weight_bound firstThreeCertificate

theorem firstThreeHighQuotient :
    (4 ^ 2 + 2 ^ 3 * 4) / 2 ^ (3 + 2) = 2 ^ (3 - 2) - 1 :=
  binary_prefix_high_quotient (by decide) firstThreeCertificate

theorem powerWeightNotLength : binaryWeight 8 = 1 ∧ (Nat.digits 2 8).length = 4 := by
  decide

theorem carryMergesOnes : binaryWeight (1 + 1) < binaryWeight 1 + binaryWeight 1 := by
  decide

theorem triangularSquareTight :
    2 * binaryWeight (5 ^ 2) = binaryWeight 5 * (binaryWeight 5 + 1) := by
  decide

theorem leadingZerosCount :
    binaryWeight (wordValue 2 [0, 0, 1, 0, 0]) = Blocks.count [1] [0, 0, 1, 0, 0] :=
  binaryWeight_wordValue (by decide)

theorem nonBinaryWordFails :
    binaryWeight (wordValue 2 [2]) ≠ Blocks.count [1] [2] := by
  decide

theorem lowerHalfWithoutUpper :
    0 ^ 2 + 2 ^ 3 * 0 ≤ (2 ^ 3) ^ 2 ∧ ¬ PrefixCertificate (2 ^ 3) 0 := by
  decide

theorem lowerHalfDoesNotGiveBound :
    ¬ 2 * 3 ≤ binaryWeight 0 ^ 2 + 3 * binaryWeight 0 + 4 := by
  decide

theorem upperHalfWithoutLower :
    (2 ^ 5) ^ 2 < (32 + 1) ^ 2 + 2 ^ 5 * (32 + 1) ∧
      ¬ PrefixCertificate (2 ^ 5) 32 := by
  decide

theorem upperHalfDoesNotGiveBound :
    ¬ 2 * 5 ≤ binaryWeight 32 ^ 2 + 3 * binaryWeight 32 + 4 := by
  decide

theorem firstThreeBinding :
    PowerOrbitAt 0 [[true], [true, false], [true, false, true]] [1, 0, 0] := by
  decide

theorem firstThreeOnes : occurrences 2 1 1 3 = 1 := by
  exact certified_power_occurrences (pattern := [1]) (by decide) (by decide)
    firstThreeBinding (by decide)

theorem firstThreeNotHalf : ¬ 3 ≤ 2 * occurrences 2 1 1 3 := by
  rw [firstThreeOnes]
  decide

theorem shiftedZeroThreeBinding :
    PowerOrbitAt 7
      [[true, false, true, false, false, false, true, false, false, false],
       [true, false, false, false, false, true, false, false, false, false, true, false],
       [true, false, false, true, false, true, false, false, true, false, true, false, true]]
      [0, 0, 0] := by
  decide

theorem shiftedZeroThreeCanonical : powerDigits 7 3 = [0, 0, 0] :=
  (powerOrbitAt_eq_powerDigits shiftedZeroThreeBinding).symm

theorem shiftedSegmentFailsPrefixBound :
    ¬ 2 * 3 ≤ Blocks.count [1] (powerDigits 7 3) ^ 2 +
      3 * Blocks.count [1] (powerDigits 7 3) + 4 := by
  rw [shiftedZeroThreeCanonical]
  decide

end GoldenNormality.SparsityCounterexamples
