import GoldenNormality.Prefix
import Mathlib.Data.List.Induction
import Mathlib.Data.Nat.Fib.Basic

/-!
# The binary golden-ratio digit automaton

The eight states and thirteen valid transitions are Figure 2 of Barnoff,
Bright and Shallit, *Computing the base-b representation of quadratic
irrationals using automata* (2026).  A ninth state makes rejection total.

The proof uses a real invariant for each state, rather than trusting the
construction program or a finite sample.  If `(q,r)` is the Fibonacci value
and its shifted value, the invariant tracks `r - phi*q`.  Reading another
digit multiplies this error by `-alpha` and, for digit one, adds `alpha^2`.
-/

namespace GoldenNormality.BinaryAutomaton

inductive State where
  | q0 | q1 | q2 | q3 | q4 | q5 | q6 | q7 | reject
  deriving DecidableEq, Repr

def step : State → Bool → State
  | .q0, false => .q0
  | .q0, true => .q1
  | .q1, false => .q2
  | .q1, true => .reject
  | .q2, false => .q3
  | .q2, true => .q4
  | .q3, false => .q5
  | .q3, true => .q6
  | .q4, false => .q2
  | .q4, true => .reject
  | .q5, false => .q7
  | .q5, true => .q1
  | .q6, false => .q5
  | .q6, true => .reject
  | .q7, false => .q5
  | .q7, true => .q1
  | .reject, _ => .reject

def output : State → Option ℕ
  | .q0 | .q2 | .q4 | .q5 => some 0
  | .q1 | .q3 | .q6 | .q7 => some 1
  | .reject => none

def runFrom : State → List Bool → State
  | s, [] => s
  | s, bit :: rest => runFrom (step s bit) rest

def run (digits : List Bool) : State := runFrom .q0 digits

def classify (digits : List Bool) : Option ℕ := output (run digits)

/-- Append a most-significant-first Fibonacci digit.  The coordinates use
weights `F_(i+2)` and `F_(i+3)`, respectively. -/
def valueStep (p : ℕ × ℕ) : Bool → ℕ × ℕ
  | false => (p.2, p.1 + p.2)
  | true => (p.2 + 1, p.1 + p.2 + 2)

def valuesFrom : ℕ × ℕ → List Bool → ℕ × ℕ
  | p, [] => p
  | p, bit :: rest => valuesFrom (valueStep p bit) rest

def values (digits : List Bool) : ℕ × ℕ := valuesFrom (0, 0) digits

noncomputable def error (p : ℕ × ℕ) : ℝ :=
  (p.2 : ℝ) - (alpha + 1) * (p.1 : ℝ)

private theorem alpha_gt_half : (1 : ℝ) / 2 < alpha := by
  by_contra h
  have hh : alpha ≤ (1 : ℝ) / 2 := le_of_not_gt h
  have hm := mul_nonneg (le_of_lt alpha_pos) (sub_nonneg.mpr hh)
  nlinarith [alpha_quadratic]

private theorem alpha_lt_two_thirds : alpha < (2 : ℝ) / 3 := by
  nlinarith [alpha_quadratic, sq_nonneg (alpha - 2 / 3)]

private theorem alpha_gt_three_fifths : (3 : ℝ) / 5 < alpha := by
  by_contra h
  have hh : alpha ≤ (3 : ℝ) / 5 := le_of_not_gt h
  have hm := mul_nonneg (le_of_lt alpha_pos) (sub_nonneg.mpr hh)
  nlinarith [alpha_quadratic]

theorem error_step (p : ℕ × ℕ) (bit : Bool) :
    error (valueStep p bit) =
      -alpha * error p + if bit then alpha ^ 2 else 0 := by
  have hq := congrArg (fun t : ℝ => t * (p.1 : ℝ)) alpha_quadratic
  cases bit <;> simp only [valueStep, error, Bool.false_eq_true, ite_false,
    ite_true, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  all_goals nlinarith [alpha_quadratic]

/-- Open intervals are essential: the output threshold is exactly one half.
The endpoints are written linearly in alpha, using alpha^2+alpha=1. -/
def ErrorInvariant (e : ℝ) : State → Prop
  | .q0 => e = 0
  | .q1 => alpha / 2 < e ∧ e < 1 / 2
  | .q2 => alpha - 1 < e ∧ e < (alpha - 1) / 2
  | .q3 => alpha - 1 / 2 < e ∧ e < 2 * alpha - 1
  | .q4 => 1 / 2 < e ∧ e < alpha
  | .q5 => (alpha - 1) / 2 < e ∧ e < 0
  | .q6 => 2 * alpha - 1 < e ∧ e < alpha / 2
  | .q7 => 0 < e ∧ e < alpha - 1 / 2
  | .reject => True

theorem invariant_step (s : State) (bit : Bool) (e : ℝ)
    (h : ErrorInvariant e s) :
    ErrorInvariant (-alpha * e + if bit then alpha ^ 2 else 0) (step s bit) := by
  have ha := alpha_pos
  have hb := alpha_lt_one
  have hc := alpha_gt_half
  have hd := alpha_lt_two_thirds
  have he := alpha_gt_three_fifths
  have hq := alpha_quadratic
  cases s <;> cases bit <;>
    simp only [step, ErrorInvariant, Bool.false_eq_true, ite_false, ite_true] at *
  all_goals try { subst e; constructor <;> nlinarith }
  all_goals try { subst e; ring }
  all_goals
    have hl := mul_lt_mul_of_pos_left h.1 ha
    have hu := mul_lt_mul_of_pos_left h.2 ha
    constructor <;> nlinarith

theorem runFrom_invariant (p : ℕ × ℕ) (s : State) (digits : List Bool)
    (h : ErrorInvariant (error p) s) :
    ErrorInvariant (error (valuesFrom p digits)) (runFrom s digits) := by
  induction digits generalizing p s with
  | nil => exact h
  | cons bit rest ih =>
    apply ih
    rw [error_step]
    exact invariant_step s bit (error p) h

theorem run_invariant (digits : List Bool) :
    ErrorInvariant (error (values digits)) (run digits) := by
  apply runFrom_invariant
  simp [ErrorInvariant, error]

/-- The input language allows leading zeroes and excludes adjacent ones. -/
def AdmissibleFrom : Bool → List Bool → Prop
  | _, [] => True
  | previous, bit :: rest => (previous = true → bit = false) ∧ AdmissibleFrom bit rest

def Admissible (digits : List Bool) : Prop := AdmissibleFrom false digits

def lastOne : State → Bool
  | .q1 | .q4 | .q6 => true
  | _ => false

theorem runFrom_nonreject_iff (s : State) (digits : List Bool) :
    runFrom s digits ≠ .reject ↔ s ≠ .reject ∧ AdmissibleFrom (lastOne s) digits := by
  induction digits generalizing s with
  | nil => simp [runFrom, AdmissibleFrom]
  | cons bit rest ih =>
    cases s <;> cases bit <;> simp [runFrom, step, ih, lastOne, AdmissibleFrom]

theorem run_nonreject_iff (digits : List Bool) :
    run digits ≠ .reject ↔ Admissible digits := by
  simpa [run, Admissible, lastOne] using runFrom_nonreject_iff .q0 digits

theorem output_ne_none_iff (s : State) : output s ≠ none ↔ s ≠ .reject := by
  cases s <;> simp [output]

theorem classify_accepts_iff (digits : List Bool) :
    classify digits ≠ none ↔ Admissible digits := by
  rw [classify, output_ne_none_iff, run_nonreject_iff]

theorem output_range {s : State} {d : ℕ} (h : output s = some d) : d < 2 := by
  cases s <;> simp only [output, Option.some.injEq, reduceCtorEq] at h <;> omega

theorem classify_range {digits : List Bool} {d : ℕ}
    (h : classify digits = some d) : d < 2 := output_range h

theorem classify_leading_zero (digits : List Bool) :
    classify (false :: digits) = classify digits := rfl

def bitValue (b : Bool) : ℕ := if b then 1 else 0

/-- The direct positional semantics: the rightmost digit has weight F_k. -/
def fibonacciSum : List Bool → ℕ → ℕ
  | [], _ => 0
  | bit :: rest, k => bitValue bit * Nat.fib (rest.length + k) + fibonacciSum rest k

theorem fibonacciSum_append_bit (digits : List Bool) (bit : Bool) (k : ℕ) :
    fibonacciSum (digits ++ [bit]) k = fibonacciSum digits (k + 1) + bitValue bit * Nat.fib k := by
  induction digits with
  | nil => simp [fibonacciSum]
  | cons head rest ih =>
    simp only [List.cons_append, fibonacciSum, List.length_append, List.length_singleton]
    rw [ih]
    have he : rest.length + 1 + k = rest.length + (k + 1) := by omega
    rw [he]
    omega

theorem fibonacciSum_recurrence (digits : List Bool) (k : ℕ) :
    fibonacciSum digits (k + 2) = fibonacciSum digits k + fibonacciSum digits (k + 1) := by
  induction digits with
  | nil => simp [fibonacciSum]
  | cons bit rest ih =>
    simp only [fibonacciSum]
    rw [show rest.length + (k + 2) = (rest.length + k) + 2 by omega,
      Nat.fib_add_two, ih]
    rw [show rest.length + (k + 1) = (rest.length + k) + 1 by omega]
    ring

theorem valuesFrom_append (p : ℕ × ℕ) (left right : List Bool) :
    valuesFrom p (left ++ right) = valuesFrom (valuesFrom p left) right := by
  induction left generalizing p with
  | nil => rfl
  | cons bit rest ih => exact ih (valueStep p bit)

theorem values_append_bit (digits : List Bool) (bit : Bool) :
    values (digits ++ [bit]) = valueStep (values digits) bit := by
  simp [values, valuesFrom_append, valuesFrom]

/-- The streaming integer evaluator has the actual Fibonacci positional value. -/
theorem values_eq_fibonacciSum (digits : List Bool) :
    values digits = (fibonacciSum digits 2, fibonacciSum digits 3) := by
  induction digits using List.reverseRecOn with
  | nil => rfl
  | append_singleton rest bit ih =>
    rw [values_append_bit, ih, fibonacciSum_append_bit, fibonacciSum_append_bit]
    have hr := fibonacciSum_recurrence rest 2
    cases bit <;> norm_num [valueStep, bitValue, Nat.fib_add_two] at * <;> omega

private theorem floor_difference_zero_error (z : ℤ) (y : ℝ) (h : (z : ℝ) - y = 0) :
    Int.floor (2 * y) - 2 * Int.floor y = 0 := by
  have hy : y = (z : ℝ) := by linarith
  rw [hy]
  have ht : (2 : ℝ) * (z : ℝ) = ((2 * z : ℤ) : ℝ) := by push_cast; rfl
  rw [ht, Int.floor_intCast, Int.floor_intCast]
  ring

private theorem floor_difference_one (z : ℤ) (y : ℝ)
    (hl : 0 < (z : ℝ) - y) (hu : (z : ℝ) - y < 1 / 2) :
    Int.floor (2 * y) - 2 * Int.floor y = 1 := by
  have hf : Int.floor y = z - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hg : Int.floor (2 * y) = 2 * z - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hf, hg]
  ring

private theorem floor_difference_zero_negative (z : ℤ) (y : ℝ)
    (hl : -(1 / 2 : ℝ) < (z : ℝ) - y) (hu : (z : ℝ) - y < 0) :
    Int.floor (2 * y) - 2 * Int.floor y = 0 := by
  have hf : Int.floor y = z := by
    rw [Int.floor_eq_iff]
    constructor <;> linarith
  have hg : Int.floor (2 * y) = 2 * z := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hf, hg]
  ring

private theorem floor_difference_zero_large (z : ℤ) (y : ℝ)
    (hl : (1 / 2 : ℝ) < (z : ℝ) - y) (hu : (z : ℝ) - y < 1) :
    Int.floor (2 * y) - 2 * Int.floor y = 0 := by
  have hf : Int.floor y = z - 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  have hg : Int.floor (2 * y) = 2 * z - 2 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  rw [hf, hg]
  ring

/-- The integer output predicate for an arbitrary input value, before
specializing that value to a power of two. -/
noncomputable def binaryDifference (q : ℕ) : ℤ :=
  Int.floor (2 * ((q : ℝ) * alpha)) - 2 * Int.floor ((q : ℝ) * alpha)

theorem output_correct (p : ℕ × ℕ) (s : State) (d : ℕ)
    (hi : ErrorInvariant (error p) s) (ho : output s = some d) :
    binaryDifference p.1 = (d : ℤ) := by
  let z : ℤ := (p.2 : ℤ) - (p.1 : ℤ)
  have he : (z : ℝ) - (p.1 : ℝ) * alpha = error p := by
    simp [z, error]
    ring
  have hzero := floor_difference_zero_error z ((p.1 : ℝ) * alpha)
  have hone := floor_difference_one z ((p.1 : ℝ) * alpha)
  have hneg := floor_difference_zero_negative z ((p.1 : ℝ) * alpha)
  have hlarge := floor_difference_zero_large z ((p.1 : ℝ) * alpha)
  rw [he] at hzero hone hneg hlarge
  have ha := alpha_pos
  have hb := alpha_lt_one
  have hc := alpha_gt_half
  have hd := alpha_lt_two_thirds
  cases s <;> simp only [ErrorInvariant] at hi <;>
    simp only [output, Option.some.injEq, reduceCtorEq] at ho
  all_goals subst d
  · exact hzero hi
  · exact hone (by linarith [hi.1]) hi.2
  · exact hneg (by linarith [hi.1]) (by linarith [hi.2])
  · exact hone (by linarith [hi.1]) (by linarith [hi.2])
  · exact hlarge hi.1 (by linarith [hi.2])
  · exact hneg (by linarith [hi.1]) hi.2
  · exact hone (by linarith [hi.1]) (by linarith [hi.2])
  · exact hone hi.1 (by linarith [hi.2])

/-- Universal correctness, for every accepted finite input word. -/
theorem classify_correct {digits : List Bool} {d : ℕ}
    (h : classify digits = some d) :
    binaryDifference (fibonacciSum digits 2) = (d : ℤ) := by
  have hc := output_correct (values digits) (run digits) d (run_invariant digits) h
  simpa only [values_eq_fibonacciSum] using hc

theorem admissible_digit_exists {digits : List Bool} (h : Admissible digits) :
    ∃ d : ℕ, d < 2 ∧ classify digits = some d ∧
      binaryDifference (fibonacciSum digits 2) = (d : ℤ) := by
  have hn := (classify_accepts_iff digits).mpr h
  cases hc : classify digits with
  | none => exact (hn hc).elim
  | some d => exact ⟨d, classify_range hc, rfl, classify_correct hc⟩

/-- A source-bound power input yields the actual zero-indexed binary digit.
The two premises are finite computable checks; the conclusion concerns alpha. -/
theorem power_input_digit {digits : List Bool} {n d : ℕ}
    (hv : fibonacciSum digits 2 = 2 ^ n) (ho : classify digits = some d) :
    GoldenNormality.digit 2 n = (d : ℤ) := by
  have hc := classify_correct ho
  rw [hv] at hc
  simpa [binaryDifference, GoldenNormality.digit, blockValue, scaledFloor,
    pow_succ, mul_assoc, mul_comm, mul_left_comm] using hc

end GoldenNormality.BinaryAutomaton
