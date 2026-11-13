import GoldenNormality.BinaryRecurrence
open GoldenNormality
example : ∀ start : ℕ,
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ digit 2 n = (0 : ℤ) :=
  binary_digit_symbol_recurs 0 0 (by decide)
