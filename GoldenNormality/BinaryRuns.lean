import GoldenNormality.BinarySparsity

/-!
# Explicit exclusion of long constant binary runs

A run beginning at zero-based position `start` has length at most `start + 1`.
The argument scales the nonzero integer residuals of the two sides of the
golden-ratio prefix certificate. It applies separately to zero and one runs;
it does not transfer the positive-polynomial sparsity proof to the complement.

Consequently every segment at positions `start` through `2 * start + 1`
contains both symbols. These estimates do not establish a positive limiting
frequency, nor any all-block normality estimate.
-/

namespace GoldenNormality

private theorem run_scale_bound {start length : ℕ} (h : start + 2 ≤ length) :
    4 * 2 ^ start ≤ 2 ^ length := by
  have hp := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) h
  simpa [pow_add, Nat.mul_comm] using hp

/-- Two actual prefix certificates exclude a zero run longer than `start + 1`.
The second prefix is bound to the first by multiplication by the run's scale. -/
theorem binary_zero_run_bound {start length q r : ℕ}
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 := by
  by_contra hlength
  have hlength' : start + 2 ≤ length := by omega
  have hscale := run_scale_bound hlength'
  have hB : 0 < 2 ^ start := by positivity
  have hD : 0 < 2 ^ length := by positivity
  have hq := certified_prefix_lt_scale hB lower
  have hstrict := binary_prefix_polynomial_lt lower
  have hgap : q ^ 2 + 2 ^ start * q + 1 ≤ (2 ^ start) ^ 2 := by omega
  have hscaled := Nat.mul_le_mul_left ((2 ^ length) ^ 2) hgap
  have hu := upper.2
  rw [run, pow_add] at hu
  have hres : (2 ^ length) ^ 2 <
      2 * (2 ^ length * q) + 2 ^ start * 2 ^ length + 1 := by
    nlinarith
  have hmq := Nat.mul_lt_mul_of_pos_left hq hD
  have hsmall : (2 ^ length) ^ 2 ≤ 3 * (2 ^ start * 2 ^ length) := by
    nlinarith
  have hlarge := Nat.mul_le_mul_left (2 ^ length) hscale
  have hproduct : 0 < 2 ^ start * 2 ^ length := Nat.mul_pos hB hD
  nlinarith

/-- Two actual prefix certificates exclude a one run longer than `start + 1`.
The `+1` on both prefix endpoints retains the carry at the end of an all-one block. -/
theorem binary_one_run_bound {start length q r : ℕ}
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r + 1 = 2 ^ length * (q + 1)) : length ≤ start + 1 := by
  by_contra hlength
  have hlength' : start + 2 ≤ length := by omega
  have hscale := run_scale_bound hlength'
  have hB : 0 < 2 ^ start := by positivity
  have hD : 0 < 2 ^ length := by positivity
  have hr := certified_prefix_lt_scale (by positivity : 0 < 2 ^ (start + length)) upper
  have hgap : (2 ^ start) ^ 2 + 1 ≤ (q + 1) ^ 2 + 2 ^ start * (q + 1) := by
    have h := lower.2
    omega
  have hscaled := Nat.mul_le_mul_left ((2 ^ length) ^ 2) hgap
  have hu := upper.1
  have hrunSquare := congrArg (fun n : ℕ => n ^ 2) run
  have hrunScale := congrArg (fun n : ℕ => 2 ^ start * 2 ^ length * n) run
  rw [pow_add] at hu hr
  have hres : (2 ^ length) ^ 2 ≤ 2 * r + 1 + 2 ^ start * 2 ^ length := by
    nlinarith
  have hlarge := Nat.mul_le_mul_left (2 ^ length) hscale
  have hproduct : 0 < 2 ^ start * 2 ^ length := Nat.mul_pos hB hD
  nlinarith

private theorem wordValue_zeroes (length : ℕ) :
    wordValue 2 (List.replicate length 0) = 0 := by
  induction length with
  | zero => rfl
  | succ length ih => simp [List.replicate_succ, wordValue, ih]

private theorem wordValue_ones_succ (length : ℕ) :
    wordValue 2 (List.replicate length 1) + 1 = 2 ^ length := by
  induction length with
  | zero => rfl
  | succ length ih =>
    simp only [List.replicate_succ, wordValue, List.length_replicate, one_mul, pow_succ]
    omega

private theorem prefix_numeral_floor (length : ℕ) :
    (wordValue 2 (BinaryAutomaton.powerDigits 0 length) : ℤ) = scaledFloor 2 length := by
  have h := (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ length)).mp
    (prefixCertificate_powerDigits length)
  simpa only [scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using h.symm

/-- Every constant segment of the total binary evaluator has length at most
its zero-based start plus one. Even the symbol is universally quantified. -/
theorem binary_power_constant_run_bound {start length d : ℕ}
    (run : BinaryAutomaton.powerDigits start length = List.replicate length d) :
    length ≤ start + 1 := by
  by_cases hzero : length = 0
  · omega
  have hd : d < 2 := by
    have ha : InAlphabet 2 (List.replicate length d) := by
      rw [← run, BinaryAutomaton.powerDigits_eq_actualDigits]
      exact actualDigits_inAlphabet (by decide) start length
    cases length with
    | zero => contradiction
    | succ length => exact ha.1
  have hv := BinaryAutomaton.wordValue_powerDigits start length
  rw [run] at hv
  simp only [blockValue, ← prefix_numeral_floor, Nat.cast_ofNat] at hv
  have hcases : d = 0 ∨ d = 1 := by omega
  rcases hcases with hd | hd
  · subst d
    rw [wordValue_zeroes] at hv
    apply binary_zero_run_bound (prefixCertificate_powerDigits start)
      (prefixCertificate_powerDigits (start + length))
    have he : (wordValue 2 (BinaryAutomaton.powerDigits 0 (start + length)) : ℤ) =
        (2 : ℤ) ^ length * wordValue 2 (BinaryAutomaton.powerDigits 0 start) := by
      simpa using (sub_eq_zero.mp hv.symm)
    exact_mod_cast he
  · subst d
    apply binary_one_run_bound (prefixCertificate_powerDigits start)
      (prefixCertificate_powerDigits (start + length))
    have hone : (wordValue 2 (List.replicate length 1) : ℤ) + 1 = (2 : ℤ) ^ length := by
      exact_mod_cast wordValue_ones_succ length
    have he : (wordValue 2 (BinaryAutomaton.powerDigits 0 (start + length)) : ℤ) + 1 =
        (2 : ℤ) ^ length * (wordValue 2 (BinaryAutomaton.powerDigits 0 start) + 1) := by
      nlinarith only [hv, hone]
    exact_mod_cast he

/-- The same constant-run bound is stated on the mathematical digit segment. -/
theorem binary_actual_constant_run_bound {start length d : ℕ}
    (run : actualDigits 2 start length = List.replicate length d) :
    length ≤ start + 1 := by
  apply binary_power_constant_run_bound (d := d)
  simpa only [BinaryAutomaton.powerDigits_eq_actualDigits] using run

/-- A supplied constant word inherits the run bound only with its actual source
position and every digit equality proved. -/
theorem certified_binary_constant_run_bound {start length d : ℕ}
    (digits : DigitsAt 2 start (List.replicate length d)) : length ≤ start + 1 := by
  have h := digitsAt_eq_actualDigits digits
  simp only [List.length_replicate] at h
  exact binary_actual_constant_run_bound h.symm

private theorem binary_word_eq_replicate_of_not_mem {text : List ℕ} {d : ℕ}
    (hd : d < 2) (alphabet : InAlphabet 2 text) (missing : d ∉ text) :
    text = List.replicate text.length (1 - d) := by
  induction text with
  | nil => rfl
  | cons a rest ih =>
    have hne : d ≠ a := by
      intro he
      exact missing (by simp [he])
    have ha : a = 1 - d := by
      have ha' := alphabet.1
      omega
    have hm : d ∉ rest := by
      intro hm
      exact missing (by simp [hm])
    simp only [List.length_cons, List.replicate_succ, ha]
    exact congrArg (List.cons (1 - d)) (ih alphabet.2 hm)

/-- Every window `[start, 2*start+2)` of actual binary digits contains each
symbol. The upper endpoint is exclusive and the window has `start + 2` digits. -/
theorem binary_actual_window_contains (start d : ℕ) (hd : d < 2) :
    d ∈ actualDigits 2 start (start + 2) := by
  by_contra hmissing
  have h := binary_word_eq_replicate_of_not_mem hd
    (actualDigits_inAlphabet (by decide : 0 < 2) start (start + 2)) hmissing
  simp only [actualDigits_length] at h
  have hbound := binary_actual_constant_run_bound h
  omega

/-- The total power evaluator has the same universal two-symbol window bound. -/
theorem binary_power_window_contains (start d : ℕ) (hd : d < 2) :
    d ∈ BinaryAutomaton.powerDigits start (start + 2) := by
  rw [BinaryAutomaton.powerDigits_eq_actualDigits]
  exact binary_actual_window_contains start d hd

end GoldenNormality
