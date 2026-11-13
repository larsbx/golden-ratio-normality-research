import GoldenNormality
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
