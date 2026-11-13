"""Source and sign controls for the actual complementary quadratic irrational.

Actual dyadic certificates fix the complement's first digits, leading-zero
blocks and shifted segments. Separate controls retain the signed convolution
coefficient and distinguish its integer boundary carry from a Euclidean
remainder. These finite facts are not asymptotic frequency evidence.
"""

COUNTEREXAMPLES = """import GoldenNormality.BinaryComplementCounts
import GoldenNormality.BinaryComplementCarry

namespace GoldenNormality.ComplementCounterexamples

theorem betaFloor0 : BinaryComplement.scaledFloor 0 = 0 :=
  BinaryComplement.scaledFloor_zero

theorem betaFloor1 : BinaryComplement.scaledFloor 1 = 0 :=
  BinaryComplement.scaledFloor_of_prefix_certificate (q := 1) (by decide) (by decide)

theorem betaFloor2 : BinaryComplement.scaledFloor 2 = 1 :=
  BinaryComplement.scaledFloor_of_prefix_certificate (q := 2) (by decide) (by decide)

theorem betaFloor3 : BinaryComplement.scaledFloor 3 = 3 :=
  BinaryComplement.scaledFloor_of_prefix_certificate (q := 4) (by decide) (by decide)

theorem betaFloor4 : BinaryComplement.scaledFloor 4 = 6 :=
  BinaryComplement.scaledFloor_of_prefix_certificate (q := 9) (by decide) (by decide)

theorem betaFloor5 : BinaryComplement.scaledFloor 5 = 12 :=
  BinaryComplement.scaledFloor_of_prefix_certificate (q := 19) (by decide) (by decide)

theorem originalFloor0 : GoldenNormality.scaledFloor 2 0 = 0 := by
  simp only [GoldenNormality.scaledFloor, pow_zero, one_mul]
  exact Int.floor_eq_zero_iff.mpr ⟨le_of_lt alpha_pos, alpha_lt_one⟩

theorem firstComplementDigit : BinaryComplement.digit 0 = 0 := by
  norm_num [BinaryComplement.digit, betaFloor0, betaFloor1]

theorem secondComplementDigit : BinaryComplement.digit 1 = 1 := by
  norm_num [BinaryComplement.digit, betaFloor1, betaFloor2]

theorem thirdComplementDigit : BinaryComplement.digit 2 = 1 := by
  norm_num [BinaryComplement.digit, betaFloor2, betaFloor3]

theorem firstOriginalDigit : GoldenNormality.digit 2 0 = 1 := by
  simpa using digit_of_certificates (b := 2) (n := 0) (q := 0) (r := 1)
    (by decide) (by decide) (by decide)

theorem leadingZeroBlock : BinaryComplement.blockValue 0 2 = 1 := by
  norm_num [BinaryComplement.blockValue, betaFloor0, betaFloor2]

theorem shiftedOneBlock : BinaryComplement.blockValue 1 2 = 3 := by
  norm_num [BinaryComplement.blockValue, betaFloor1, betaFloor3]

theorem firstTwoComplement : BinaryComplement.actualDigits 0 2 = [0, 1] := by
  norm_num [BinaryComplement.actualDigits, List.range_succ,
    firstComplementDigit, secondComplementDigit]

theorem shiftedTwoComplement : BinaryComplement.actualDigits 1 2 = [1, 1] := by
  norm_num [BinaryComplement.actualDigits, List.range_succ,
    secondComplementDigit, thirdComplementDigit]

theorem fixedWidthFlip :
    BinaryComplement.flipValue 2 1 = 2 ∧ BinaryComplement.flipValue 1 1 = 0 := by
  decide

theorem emptyWidthFlip : BinaryComplement.flipValue 0 0 = 0 := by decide

theorem invalidFlipNotInvolution :
    BinaryComplement.flipValue 1 (BinaryComplement.flipValue 1 2) ≠ 2 := by
  decide

theorem originalFirstThreeBinding : DigitsAt 2 0 [1, 0, 0] := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · simpa using digit_of_certificates (b := 2) (n := 0) (q := 0) (r := 1)
      (by decide) (by decide) (by decide)
  · simpa using digit_of_certificates (b := 2) (n := 1) (q := 1) (r := 2)
      (by decide) (by decide) (by decide)
  · simpa using digit_of_certificates (b := 2) (n := 2) (q := 2) (r := 4)
      (by decide) (by decide) (by decide)

theorem firstThreeOriginalCounts :
    GoldenNormality.occurrences 2 1 0 3 = 2 ∧
      GoldenNormality.occurrences 2 1 1 3 = 1 := by
  constructor
  · simpa [wordValue] using certified_occurrences_sound (pattern := [0])
      (by decide) (by decide) (by decide) originalFirstThreeBinding (by decide)
  · simpa [wordValue] using certified_occurrences_sound (pattern := [1])
      (by decide) (by decide) (by decide) originalFirstThreeBinding (by decide)

theorem firstThreeComplementCounts :
    BinaryComplement.occurrences 1 1 3 = 2 ∧ BinaryComplement.occurrences 1 0 3 = 1 := by
  rw [BinaryComplement.ones_eq_original_zeros, BinaryComplement.zeros_eq_original_ones]
  exact firstThreeOriginalCounts

theorem firstTwoComplementOneCount : BinaryComplement.occurrences 1 1 2 = 1 := by
  rw [BinaryComplement.ones_eq_original_zeros]
  have h : DigitsAt 2 0 [1, 0] :=
    ⟨originalFirstThreeBinding.1, originalFirstThreeBinding.2.1, trivial⟩
  simpa [wordValue] using certified_occurrences_sound (pattern := [0])
    (by decide) (by decide) (by decide) h (by decide)

theorem firstTwoComplementPower : BinaryComplement.powerDigits 0 2 = [0, 1] :=
  (BinaryComplement.powerDigits_eq_actualDigits 0 2).trans firstTwoComplement

theorem shiftedTwoComplementPower : BinaryComplement.powerDigits 1 2 = [1, 1] :=
  (BinaryComplement.powerDigits_eq_actualDigits 1 2).trans shiftedTwoComplement

theorem normalityRetainsEquivalence :
    BinaryComplement.Normal ↔ GoldenNormality.NormalInBase 2 :=
  BinaryComplement.normal_iff_original

theorem positiveLinearPolynomialFails :
    BinaryComplement.beta ^ 2 + 3 * BinaryComplement.beta + 1 ≠ 0 := by
  have h := BinaryComplement.beta_pos
  nlinarith [sq_nonneg BinaryComplement.beta]

theorem carryFirstValues :
    BinaryComplement.carry 0 = -1 ∧ BinaryComplement.carry 1 = -2 ∧
      BinaryComplement.carry 2 = -1 ∧ BinaryComplement.carry 3 = 1 := by
  norm_num [BinaryComplement.carry, BinaryComplement.convolutionPrefix,
    Finset.sum_range_succ, betaFloor0, betaFloor1, betaFloor2, betaFloor3,
    firstComplementDigit, secondComplementDigit, thirdComplementDigit]

theorem firstSignedCoefficients :
    BinaryComplement.signedCoefficient 0 = 0 ∧
      BinaryComplement.signedCoefficient 1 = -3 ∧
        BinaryComplement.signedCoefficient 2 = -3 := by
  norm_num [BinaryComplement.signedCoefficient, BinaryComplement.convolutionCoefficient,
    Finset.sum_range_succ, firstComplementDigit, secondComplementDigit, thirdComplementDigit]

theorem firstNonzeroConvolution : BinaryComplement.convolutionCoefficient 3 = 1 := by
  norm_num [BinaryComplement.convolutionCoefficient, Finset.sum_range_succ,
    firstComplementDigit, secondComplementDigit, thirdComplementDigit]

theorem laterCarryValues :
    BinaryComplement.carry 4 = 1 ∧ BinaryComplement.carry 5 = 0 ∧
      BinaryComplement.digit 4 = 0 := by
  norm_num [BinaryComplement.carry, BinaryComplement.convolutionPrefix,
    Finset.sum_range_succ, BinaryComplement.digit,
    betaFloor0, betaFloor1, betaFloor2, betaFloor3, betaFloor4, betaFloor5]

theorem uncarriedSuffixExceedsScale : BinaryComplement.convolutionSuffix 4 = 20 := by
  norm_num [BinaryComplement.convolutionSuffix, Finset.sum_range_succ,
    BinaryComplement.digit, BinaryComplement.blockValue,
    betaFloor0, betaFloor1, betaFloor2, betaFloor3, betaFloor4]

theorem carryCrossesZero :
    2 * BinaryComplement.carry 2 =
      BinaryComplement.carry 3 + BinaryComplement.signedCoefficient 2 := by
  rw [carryFirstValues.2.2.1, carryFirstValues.2.2.2, firstSignedCoefficients.2.2]
  decide

theorem boundaryCarryNotRemainder :
    BinaryComplement.carry 0 ≠ BinaryComplement.prefixResidual 0 % (2 : ℤ) ^ 0 := by
  rw [carryFirstValues.1]
  norm_num [BinaryComplement.prefixResidual, BinaryComplement.quadraticResidual, betaFloor0]

theorem leadingZeroWidthRetained :
    (BinaryComplement.actualDigits 0 2).length = 2 ∧
      wordValue 2 (BinaryComplement.actualDigits 0 2) = 1 := by
  rw [firstTwoComplement]
  decide

theorem actualThreeZeroCarryTrigger : 0 < BinaryComplement.carry 3 := by
  have hfloor6 : BinaryComplement.scaledFloor 6 = 24 :=
    BinaryComplement.scaledFloor_of_prefix_certificate (q := 39) (by decide) (by decide)
  apply BinaryComplement.carry_positive_of_convolution_three_zeroes 3
  · rw [firstNonzeroConvolution]
    decide
  · norm_num [BinaryComplement.digit, betaFloor3, betaFloor4]
  · exact laterCarryValues.2.2
  · norm_num [BinaryComplement.digit, betaFloor5, hfloor6]

theorem actualTwoZeroTriggerFails :
    BinaryComplement.convolutionCoefficient 5 = 1 ∧
      BinaryComplement.digit 5 = 0 ∧ BinaryComplement.digit 6 = 0 ∧
        BinaryComplement.carry 5 = 0 := by
  have hfloor6 : BinaryComplement.scaledFloor 6 = 24 :=
    BinaryComplement.scaledFloor_of_prefix_certificate (q := 39) (by decide) (by decide)
  have hfloor7 : BinaryComplement.scaledFloor 7 = 48 :=
    BinaryComplement.scaledFloor_of_prefix_certificate (q := 79) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, laterCarryValues.2.1⟩
  · norm_num [BinaryComplement.convolutionCoefficient, Finset.sum_range_succ,
      BinaryComplement.digit, betaFloor0, betaFloor1, betaFloor2, betaFloor3, betaFloor4, betaFloor5]
  · norm_num [BinaryComplement.digit, betaFloor5, hfloor6]
  · norm_num [BinaryComplement.digit, hfloor6, hfloor7]

end GoldenNormality.ComplementCounterexamples
"""

REJECTIONS = {
    "complement_floor_without_minus_one": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.scaledFloor 0 = (2 : ℤ) ^ 0 - GoldenNormality.scaledFloor 2 0 := by
  rw [betaFloor0, originalFloor0]
  decide
""", r"(?i)decide.*proved"),
    "complement_digit_without_source_flip": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.digit 0 = GoldenNormality.digit 2 0 := by
  rw [firstComplementDigit, firstOriginalDigit]
  decide
""", r"(?i)decide.*proved"),
    "complement_reset_shifted_origin": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.actualDigits 1 2 = BinaryComplement.actualDigits 0 2 := by
  rw [shiftedTwoComplement, firstTwoComplement]
  decide
""", r"(?i)decide.*proved"),
    "complement_erase_leading_zero_width": ("""import GoldenNormality.BinaryComplementCounts
open GoldenNormality.BinaryComplement
example : flipValue 2 1 = flipValue 1 1 := by decide
""", r"(?i)decide.*proved"),
    "complement_out_of_range_involution": ("""import GoldenNormality.BinaryComplementCounts
open GoldenNormality.BinaryComplement
example : flipValue 1 (flipValue 1 2) = 2 := by decide
""", r"(?i)decide.*proved"),
    "complement_count_without_symbol_swap": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.occurrences 1 1 3 = GoldenNormality.occurrences 2 1 1 3 := by
  rw [firstThreeComplementCounts.1, firstThreeOriginalCounts.2]
  decide
""", r"(?i)decide.*proved"),
    "complement_shifted_count_as_prefix": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : Blocks.count [1] (BinaryComplement.powerDigits 1 2) =
    BinaryComplement.occurrences 1 1 2 := by
  rw [shiftedTwoComplementPower, firstTwoComplementOneCount]
  decide
""", r"(?i)decide.*proved"),
    "complement_positive_linear_coefficient": ("""import GoldenNormality.BinaryComplement
open GoldenNormality.BinaryComplement
example : beta ^ 2 + 3 * beta + 1 = 0 := beta_quadratic
""", r"(?i)type mismatch"),
    "complement_carry_recurrence_wrong_sign": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 2 * BinaryComplement.carry 2 =
    BinaryComplement.carry 3 - BinaryComplement.signedCoefficient 2 := by
  rw [carryFirstValues.2.2.1, carryFirstValues.2.2.2, firstSignedCoefficients.2.2]
  decide
""", r"(?i)decide.*proved"),
    "complement_backward_positivity_without_zero": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.carry 3 → 0 < BinaryComplement.carry 2 := by
  rw [carryFirstValues.2.2.2, carryFirstValues.2.2.1]
  intro _
  decide
""", r"(?i)decide.*proved"),
    "complement_forward_positivity_through_zero": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.carry 4 → BinaryComplement.digit 4 = 0 →
    0 < BinaryComplement.carry 5 := by
  rw [laterCarryValues.1, laterCarryValues.2.2, laterCarryValues.2.1]
  intro _ _
  decide
""", r"(?i)decide.*proved"),
    "complement_uncarried_suffix_as_small_remainder": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.convolutionSuffix 4 < (2 : ℤ) ^ 4 := by
  rw [uncarriedSuffixExceedsScale]
  decide
""", r"(?i)decide.*proved"),
    "complement_two_zeroes_as_three_zero_trigger": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : 0 < BinaryComplement.convolutionCoefficient 5 →
    BinaryComplement.digit 5 = 0 → BinaryComplement.digit 6 = 0 →
      0 < BinaryComplement.carry 5 := by
  rw [actualTwoZeroTriggerFails.1, actualTwoZeroTriggerFails.2.1,
    actualTwoZeroTriggerFails.2.2.1, actualTwoZeroTriggerFails.2.2.2]
  intro _ _ _
  decide
""", r"(?i)decide.*proved"),
    "complement_boundary_carry_as_remainder": ("""import ComplementCounterexamples
open GoldenNormality GoldenNormality.ComplementCounterexamples
example : BinaryComplement.carry 0 = BinaryComplement.prefixResidual 0 % (2 : ℤ) ^ 0 := by
  rw [carryFirstValues.1]
  norm_num only [BinaryComplement.prefixResidual, BinaryComplement.quadraticResidual,
    betaFloor0, pow_zero]
  decide
""", r"(?i)decide.*proved"),
    "complement_normality_one_way_as_iff": ("""import GoldenNormality.BinaryComplementCounts
open GoldenNormality.BinaryComplement
example : Normal ↔ GoldenNormality.NormalInBase 2 := normal_iff_original.mp
""", r"(?i)type mismatch"),
}
