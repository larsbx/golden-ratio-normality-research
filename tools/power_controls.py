"""Source-binding counterexamples and rejection controls for power-orbit traces."""

COUNTEREXAMPLES = """import GoldenNormality
namespace GoldenNormality.PowerOrbitCounterexamples
open BinaryAutomaton

theorem firstFour :
    PowerOrbitAt 0 [[true], [true, false], [true, false, true],
      [true, false, false, false, false]] [1, 0, 0, 1] := by decide

theorem leadingZerosAllowed :
    PowerOrbitAt 0 [[false, true], [false, true, false], [false, true, false, true],
      [false, true, false, false, false, false]] [1, 0, 0, 1] := by decide

theorem actualFirstFour : DigitsAt 2 0 [1, 0, 0, 1] := powerOrbitAt_digitsAt firstFour

theorem canonicalFirstFour : [1, 0, 0, 1] = powerDigits 0 4 :=
  powerOrbitAt_eq_powerDigits firstFour

theorem shiftedSecond : PowerOrbitAt 1 [[true, false]] [0] := by decide

theorem shiftedSecondNotPrefix : ¬ PowerOrbitAt 0 [[true, false]] [0] := by decide

theorem zeroInputAccepted : classify [false] = some 0 ∧ fibonacciSum [false] 2 = 0 := by decide

theorem zeroInputNotPower : ¬ PowerOrbitAt 0 [[false]] [0] := by decide

theorem ordinalInputsAccepted :
    classify [true] = some 1 ∧ classify [true, false] = some 0 ∧
      classify [true, false, false] = some 1 ∧ classify [true, false, true] = some 0 := by decide

theorem ordinalInputsNotPowers :
    ¬ PowerOrbitAt 0 [[true], [true, false], [true, false, false], [true, false, true]]
      [1, 0, 1, 0] := by decide

theorem unequalTraceLengths : ¬ PowerOrbitAt 0 [[true]] [1, 0] := by decide

theorem emptyTrace (start : ℕ) : PowerOrbitAt start [] [] := True.intro

end GoldenNormality.PowerOrbitCounterexamples
"""

REJECTIONS = {
    "non_power_input": ("""import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 0 [[false]] [0] := by decide
""", r"(?i)decide.*proved"),
    "shifted_power_position": ("""import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 1 [[true]] [1] := by decide
""", r"(?i)decide.*proved"),
    "mismatched_orbit_lengths": ("""import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 0 [[true]] [1, 0] := by decide
""", r"(?i)decide.*proved"),
    "incorrect_power_output": ("""import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 1 [[true, false]] [1] := by decide
""", r"(?i)decide.*proved"),
    "ordinal_inputs_as_powers": ("""import GoldenNormality
open GoldenNormality.BinaryAutomaton
example : PowerOrbitAt 0 [[true], [true, false], [true, false, false], [true, false, true]]
    [1, 0, 1, 0] := by decide
""", r"(?i)decide.*proved"),
    "weakened_power_source": ("""import Receipts
open GoldenNormality
example : DigitsAt 2 0 Receipts.powerWord_4 := Receipts.powerDigits_4
""", r"(?i)type mismatch"),
    "weakened_power_normality_type": ("""import GoldenNormality
open GoldenNormality GoldenNormality.BinaryAutomaton
namespace WeakenedPowerNormality
theorem onlyForward : PowerOrbitNormality → NormalInBase 2 :=
  powerOrbitNormality_iff_normalInBase.mp
example : PowerOrbitNormality ↔ NormalInBase 2 := onlyForward
end WeakenedPowerNormality
""", r"(?i)type mismatch"),
}
