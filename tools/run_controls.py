"""Source-bound controls for binary runs, recurrence, and symbol counts.

Adjacent prefix certificates certify the actual zero run at start 1 and one
run at start 3. The controls retain the original positions, endpoint exponents,
one-run carry, binary alphabet, and universal recurrence quantifiers.
"""

COUNTEREXAMPLES = """import GoldenNormality.BinaryRecurrence
namespace GoldenNormality.RunCounterexamples
open BinaryAutomaton

theorem prefix0 : PrefixCertificate (2 ^ 0) 0 := by decide
theorem prefix1 : PrefixCertificate (2 ^ 1) 1 := by decide
theorem prefix2 : PrefixCertificate (2 ^ 2) 2 := by decide
theorem prefix3 : PrefixCertificate (2 ^ 3) 4 := by decide
theorem prefix4 : PrefixCertificate (2 ^ 4) 9 := by decide
theorem prefix5 : PrefixCertificate (2 ^ 5) 19 := by decide
theorem prefix6 : PrefixCertificate (2 ^ 6) 39 := by decide
theorem prefix7 : PrefixCertificate (2 ^ 7) 79 := by decide

theorem firstTwoBinding : DigitsAt 2 0 [1, 0] := by
  refine ⟨?_, ?_, trivial⟩
  · simpa using digit_of_certificates (b := 2) (n := 0) (by decide) prefix0 prefix1
  · simpa using digit_of_certificates (b := 2) (n := 1) (by decide) prefix1 prefix2

theorem zeroTwoBinding : DigitsAt 2 1 [0, 0] := by
  refine ⟨?_, ?_, trivial⟩
  · simpa using digit_of_certificates (b := 2) (n := 1) (by decide) prefix1 prefix2
  · simpa using digit_of_certificates (b := 2) (n := 2) (by decide) prefix2 prefix3

theorem oneFourBinding : DigitsAt 2 3 [1, 1, 1, 1] := by
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · simpa using digit_of_certificates (b := 2) (n := 3) (by decide) prefix3 prefix4
  · simpa using digit_of_certificates (b := 2) (n := 4) (by decide) prefix4 prefix5
  · simpa using digit_of_certificates (b := 2) (n := 5) (by decide) prefix5 prefix6
  · simpa using digit_of_certificates (b := 2) (n := 6) (by decide) prefix6 prefix7

theorem firstTwoActual : actualDigits 2 0 2 = [1, 0] :=
  (digitsAt_eq_actualDigits firstTwoBinding).symm

theorem zeroTwoActual : actualDigits 2 1 2 = [0, 0] :=
  (digitsAt_eq_actualDigits zeroTwoBinding).symm

theorem oneFourActual : actualDigits 2 3 4 = [1, 1, 1, 1] :=
  (digitsAt_eq_actualDigits oneFourBinding).symm

theorem firstTwoCanonical : powerDigits 0 2 = [1, 0] :=
  (powerDigits_eq_actualDigits 0 2).trans firstTwoActual

theorem zeroTwoCanonical : powerDigits 1 2 = [0, 0] :=
  (powerDigits_eq_actualDigits 1 2).trans zeroTwoActual

theorem oneFourCanonical : powerDigits 3 4 = [1, 1, 1, 1] :=
  (powerDigits_eq_actualDigits 3 4).trans oneFourActual

theorem zeroTwoArithmeticBound : 2 ≤ 1 + 1 :=
  binary_zero_run_bound prefix1 prefix3 (by decide)

theorem oneFourArithmeticBound : 4 ≤ 3 + 1 :=
  binary_one_run_bound prefix3 prefix7 (by decide)

theorem oneFourPowerBound : 4 ≤ 3 + 1 :=
  binary_power_constant_run_bound (by simpa using oneFourCanonical)

theorem zeroTwoActualBound : 2 ≤ 1 + 1 :=
  binary_actual_constant_run_bound (by simpa using zeroTwoActual)

theorem oneFourCertifiedBound : 4 ≤ 3 + 1 :=
  certified_binary_constant_run_bound (start := 3) (length := 4) (d := 1) oneFourBinding

theorem emptyPowerRun (start d : ℕ) : 0 ≤ start + 1 :=
  binary_power_constant_run_bound (start := start) (length := 0) (d := d) rfl

theorem zeroTwoSharp : (powerDigits 1 2).length = 1 + 1 := by
  rw [zeroTwoCanonical]
  rfl

theorem oneFourSharp : (powerDigits 3 4).length = 3 + 1 := by
  rw [oneFourCanonical]
  rfl

theorem zeroTwoRefutesShorterBound : ¬ (powerDigits 1 2).length ≤ 1 := by
  rw [zeroTwoCanonical]
  decide

theorem oneFourRefutesShorterBound : ¬ (powerDigits 3 4).length ≤ 3 := by
  rw [oneFourCanonical]
  decide

theorem zeroTwoMissesOne : 1 ∉ powerDigits 1 (1 + 1) := by
  rw [zeroTwoCanonical]
  decide

theorem firstTwoContainBoth : 0 ∈ powerDigits 0 2 ∧ 1 ∈ powerDigits 0 2 := by
  rw [firstTwoCanonical]
  decide

theorem firstTwoExcludeNonbinary : 2 ∉ powerDigits 0 2 := by
  rw [firstTwoCanonical]
  decide

theorem zeroTwoCannotResetOrigin : ¬ DigitsAt 2 0 [0, 0] := by
  intro h
  have hzero := h.1
  have hone := firstTwoBinding.1
  omega

theorem firstTwoZeroCount : occurrences 2 1 0 2 = 1 := by
  simpa [wordValue] using certified_occurrences_sound (pattern := [0])
    (by decide) (by decide) (by decide) firstTwoBinding (by decide)

theorem firstTwoOneCount : occurrences 2 1 1 2 = 1 := by
  simpa [wordValue] using certified_occurrences_sound (pattern := [1])
    (by decide) (by decide) (by decide) firstTwoBinding (by decide)

theorem checkpointZeroSymbol : 1 ≤ occurrences 2 1 0 2 := by
  simpa using binary_occurrences_logarithmic_bound 1 0 (by decide)

theorem checkpointOneSymbol : 2 ≤ occurrences 2 1 1 6 := by
  simpa using binary_occurrences_logarithmic_bound 2 1 (by decide)

theorem emptyCheckpoint : 0 ≤ occurrences 2 1 0 0 :=
  binary_occurrences_logarithmic_bound 0 0 (by decide)

theorem wrongCheckpointFails : ¬ 1 ≤ occurrences 2 1 0 (2 ^ 1 - 2) := by
  change ¬ 1 ≤ occurrences 2 1 0 0
  rw [occurrences_zero]
  decide

theorem seventhPrefixPartition :
    occurrences 2 1 0 7 + occurrences 2 1 1 7 = 7 :=
  binary_occurrences_partition 7

theorem sixthPrefixTwoSided :
    2 ≤ occurrences 2 1 1 6 ∧ occurrences 2 1 1 6 + 2 ≤ 6 :=
  binary_occurrences_two_sided 2 6 (by decide)

theorem allStartActualWitness (start d : ℕ) (hd : d < 2) :
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ digit 2 n = (d : ℤ) :=
  binary_digit_symbol_recurs start d hd

theorem allStartPowerWindow (start d : ℕ) (hd : d < 2) :
    d ∈ powerDigits start (start + 2) :=
  binary_power_window_contains start d hd

end GoldenNormality.RunCounterexamples
"""

REJECTIONS = {
    "run_lower_half_as_certificate": ("""import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length q r : ℕ)
    (lower : q ^ 2 + 2 ^ start * q ≤ (2 ^ start) ^ 2)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_zero_run_bound lower upper run
""", r"(?i)type mismatch"),
    "shifted_run_endpoint": ("""import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length q r : ℕ)
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length + 1)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_zero_run_bound lower upper run
""", r"(?i)type mismatch"),
    "arbitrary_word_as_run_source": ("""import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length d : ℕ) (text : List ℕ)
    (run : text = List.replicate length d) : length ≤ start + 1 :=
  certified_binary_constant_run_bound run
""", r"(?i)type mismatch"),
    "reset_run_source_origin": ("""import RunCounterexamples
open GoldenNormality GoldenNormality.RunCounterexamples
example : DigitsAt 2 0 [0, 0] := zeroTwoBinding
""", r"(?i)type mismatch"),
    "run_bound_without_additive_one": ("""import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : (powerDigits 1 2).length ≤ 1 := by
  rw [zeroTwoCanonical]
  decide
""", r"(?i)decide.*proved"),
    "shortened_binary_window": ("""import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : 1 ∈ powerDigits 1 (1 + 1) := by
  rw [zeroTwoCanonical]
  decide
""", r"(?i)decide.*proved"),
    "nonbinary_recurrence_symbol": ("""import RunCounterexamples
open GoldenNormality.BinaryAutomaton GoldenNormality.RunCounterexamples
example : 2 ∈ powerDigits 0 (0 + 2) := by
  rw [firstTwoCanonical]
  decide
""", r"(?i)decide.*proved"),
    "recurrence_checkpoint_missing_exponent_one": ("""import GoldenNormality.BinaryRecurrence
open GoldenNormality
example : 1 ≤ occurrences 2 1 0 (2 ^ 1 - 2) := by
  change 1 ≤ occurrences 2 1 0 0
  rw [occurrences_zero]
  decide
""", r"(?i)decide.*proved"),
    "finite_recurrence_as_all_starts": ("""import GoldenNormality.BinaryRecurrence
open GoldenNormality
example : ∀ start : ℕ,
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ digit 2 n = (0 : ℤ) :=
  binary_digit_symbol_recurs 0 0 (by decide)
""", r"(?i)type mismatch"),
    "one_run_missing_endpoint_carry": ("""import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length q r : ℕ)
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_one_run_bound lower upper run
""", r"(?i)type mismatch"),
}
