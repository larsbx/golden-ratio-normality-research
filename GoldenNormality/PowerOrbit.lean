import GoldenNormality.ZeckendorfEncoding
import GoldenNormality.NormalityCriteria

/-!
# Total evaluation on the power-of-two orbit

The canonical Fibonacci encoder makes the proved automaton a total computable
evaluator on natural inputs. Its outputs at `2^n` are exactly the actual binary
digits at the zero-based position `n`. Finite output words therefore have the
same block counts as the mathematical digit sequence.

The separate finite witness relation accepts any input representations whose
values and classifier outputs have been proved. It does not require a native
encoder to agree with the canonical Lean encoder. Normality remains an open
eventual-frequency statement, now also stated on the computable output words.
-/

namespace GoldenNormality.BinaryAutomaton

/-- Total computable evaluation; the fallback is proved unreachable below. -/
def evaluated (q : ℕ) : ℕ := (classify (encode q)).getD 0

/-- The canonical encoded input is always accepted with its evaluated output. -/
theorem classify_encode (q : ℕ) : classify (encode q) = some (evaluated q) := by
  have hn := (classify_accepts_iff (encode q)).mpr (encode_admissible q)
  cases hc : classify (encode q) with
  | none => exact (hn hc).elim
  | some d => simp [evaluated, hc]

theorem evaluated_lt_two (q : ℕ) : evaluated q < 2 :=
  classify_range (classify_encode q)

/-- The total computable evaluator has the automaton's real-number semantics. -/
theorem evaluated_correct (q : ℕ) : binaryDifference q = (evaluated q : ℤ) := by
  simpa only [fibonacciSum_encode] using classify_correct (classify_encode q)

/-- The computable output at the input representing `2^n`. -/
def powerDigit (n : ℕ) : ℕ := evaluated (2 ^ n)

theorem powerDigit_lt_two (n : ℕ) : powerDigit n < 2 := evaluated_lt_two (2 ^ n)

/-- Every power-orbit output is the actual binary fractional digit at its index. -/
theorem powerDigit_correct (n : ℕ) : digit 2 n = (powerDigit n : ℤ) :=
  power_input_digit (fibonacciSum_encode (2 ^ n)) (classify_encode (2 ^ n))

/-- A computable segment retaining its original starting position. -/
def powerDigits : ℕ → ℕ → List ℕ
  | _, 0 => []
  | start, length + 1 => powerDigit start :: powerDigits (start + 1) length

@[simp] theorem powerDigits_zero (start : ℕ) : powerDigits start 0 = [] := rfl

theorem powerDigits_succ (start length : ℕ) :
    powerDigits start (length + 1) = powerDigit start :: powerDigits (start + 1) length := rfl

@[simp] theorem powerDigits_length (start length : ℕ) :
    (powerDigits start length).length = length := by
  induction length generalizing start with
  | zero => rfl
  | succ length ih => simp only [powerDigits, List.length_cons, ih]

theorem powerDigits_digitsAt (start length : ℕ) :
    DigitsAt 2 start (powerDigits start length) := by
  induction length generalizing start with
  | zero => trivial
  | succ length ih => exact ⟨powerDigit_correct start, ih (start + 1)⟩

/-- The computable and mathematical digit segments agree at every start and length. -/
theorem powerDigits_eq_actualDigits (start length : ℕ) :
    powerDigits start length = actualDigits 2 start length := by
  simpa only [powerDigits_length] using
    digitsAt_eq_actualDigits (powerDigits_digitsAt start length)

theorem wordValue_powerDigits (start length : ℕ) :
    (wordValue 2 (powerDigits start length) : ℤ) = blockValue 2 start length := by
  rw [powerDigits_eq_actualDigits]
  exact wordValue_actualDigits 2 start length

/-- The first `N` complete starts of a nonempty binary pattern are counted exactly. -/
theorem count_powerDigits {pattern : List ℕ} (hpat : pattern ≠ [])
    (ha : InAlphabet 2 pattern) (N : ℕ) :
    Blocks.count pattern (powerDigits 0 (N + pattern.length - 1)) =
      occurrences 2 pattern.length (wordValue 2 pattern) N := by
  rw [powerDigits_eq_actualDigits]
  exact count_actualDigits_prefix (by decide) hpat ha N

/-- The open binary normality target on the total computable power-orbit outputs.
All nonempty binary words and positive tolerances retain every sufficiently
large number of starts; the threshold may depend on the word and tolerance.
-/
def PowerOrbitNormality : Prop :=
  ∀ pattern : List ℕ, pattern ≠ [] → InAlphabet 2 pattern →
    ∀ toleranceDenominator : ℕ, 1 ≤ toleranceDenominator →
      ∃ N0 : ℕ, 1 ≤ N0 ∧
        ∀ N : ℕ, N0 ≤ N →
          Nat.dist ((2 ^ pattern.length) *
            Blocks.count pattern (powerDigits 0 (N + pattern.length - 1))) N *
              toleranceDenominator ≤ N

/-- Computability changes the presentation of the target, not its quantifiers. -/
theorem powerOrbitNormality_iff_normalInBase : PowerOrbitNormality ↔ NormalInBase 2 := by
  constructor
  · intro h
    apply (normalInBase_iff_normalByWords 2).mpr
    refine ⟨by decide, ?_⟩
    intro pattern hpat ha tolerance htol
    obtain ⟨N0, hN0, hbound⟩ := h pattern hpat ha tolerance htol
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    simpa only [powerDigits_eq_actualDigits] using hbound N hN
  · intro h
    have hw := (normalInBase_iff_normalByWords 2).mp h
    intro pattern hpat ha tolerance htol
    obtain ⟨N0, hN0, hbound⟩ := hw.2 pattern hpat ha tolerance htol
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    rw [powerDigits_eq_actualDigits]
    exact hbound N hN

/-- A finite source-bound trace. Each representation must have the stated power
value and accepted output. Unequal numbers of inputs and outputs are rejected.
Representations may include leading zeros and need not equal `encode`.
-/
def PowerOrbitAt (start : ℕ) : List (List Bool) → List ℕ → Prop
  | [], [] => True
  | input :: inputs, d :: outputs =>
      fibonacciSum input 2 = 2 ^ start ∧ classify input = some d ∧
        PowerOrbitAt (start + 1) inputs outputs
  | [], _ :: _ => False
  | _ :: _, [] => False

instance (start : ℕ) (inputs : List (List Bool)) (outputs : List ℕ) :
    Decidable (PowerOrbitAt start inputs outputs) := by
  induction inputs generalizing start outputs with
  | nil =>
    cases outputs with
    | nil => exact isTrue True.intro
    | cons d outputs => exact isFalse (fun h => h)
  | cons input inputs ih =>
    cases outputs with
    | nil => exact isFalse (fun h => h)
    | cons d outputs =>
      change Decidable (fibonacciSum input 2 = 2 ^ start ∧ classify input = some d ∧
        PowerOrbitAt (start + 1) inputs outputs)
      letI : Decidable (PowerOrbitAt (start + 1) inputs outputs) := ih (start + 1) outputs
      infer_instance

theorem powerOrbitAt_length {start : ℕ} {inputs : List (List Bool)} {outputs : List ℕ}
    (h : PowerOrbitAt start inputs outputs) : inputs.length = outputs.length := by
  induction inputs generalizing start outputs with
  | nil =>
    cases outputs with
    | nil => rfl
    | cons d outputs => exact h.elim
  | cons input inputs ih =>
    cases outputs with
    | nil => exact h.elim
    | cons d outputs => exact congrArg Nat.succ (ih h.2.2)

theorem powerOrbitAt_digitsAt {start : ℕ} {inputs : List (List Bool)} {outputs : List ℕ}
    (h : PowerOrbitAt start inputs outputs) : DigitsAt 2 start outputs := by
  induction inputs generalizing start outputs with
  | nil =>
    cases outputs with
    | nil => trivial
    | cons d outputs => exact h.elim
  | cons input inputs ih =>
    cases outputs with
    | nil => exact h.elim
    | cons d outputs => exact ⟨power_input_digit h.1 h.2.1, ih h.2.2⟩

/-- A certified trace agrees with the canonical output segment without requiring
its individual representations to be canonical or evaluating that encoder.
-/
theorem powerOrbitAt_eq_powerDigits {start : ℕ} {inputs : List (List Bool)}
    {outputs : List ℕ} (h : PowerOrbitAt start inputs outputs) :
    outputs = powerDigits start outputs.length := by
  rw [powerDigits_eq_actualDigits]
  exact digitsAt_eq_actualDigits (powerOrbitAt_digitsAt h)

/-- A source-bound trace beginning at zero gives the exact first-start count.
The literal start `0` is essential; arbitrary shifted traces concern segments.
-/
theorem certified_power_occurrences {value : ℕ} {inputs : List (List Bool)}
    {outputs pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet 2 pattern)
    (orbit : PowerOrbitAt 0 inputs outputs) (count : Blocks.count pattern outputs = value) :
    occurrences 2 pattern.length (wordValue 2 pattern) (outputs.length + 1 - pattern.length) =
      value :=
  certified_occurrences_sound (by decide) hpat ha (powerOrbitAt_digitsAt orbit) count

end GoldenNormality.BinaryAutomaton
