import GoldenNormality.Prefix
import Mathlib.Data.Nat.Dist
import Init.Data.List.Count
import Init.Data.List.Range

/-!
# The open normality target

This module states a target for the actual fractional digits of the golden
ratio, using `blockValue` from `GoldenNormality.Prefix`.  It does not assert that
the target holds in any base.

Starting positions are zero-indexed.  For `N` starts, a block of length `k` is
tested at every position in `0, ..., N - 1`, with overlaps retained.  Thus, when
`N` and `k` are positive, these observations require `N + k - 1` fractional
digits.  A block value `j < b ^ k` also represents words with leading zeros.
-/

namespace GoldenNormality

noncomputable section

/-- The number of occurrences of the length-`k` block with value `j` among the
first `N` starting positions of the actual base-`b` fractional expansion.

This is a mathematical count over the real-number definition of `blockValue`,
not an executable claim about an unverified digit producer.
-/
def occurrences (b k j N : ℕ) : ℕ :=
  (List.range N).countP (fun n => decide (blockValue b n k = (j : ℤ)))

@[simp]
theorem occurrences_zero (b k j : ℕ) : occurrences b k j 0 = 0 := by
  simp [occurrences]

theorem occurrences_le_N (b k j N : ℕ) : occurrences b k j N ≤ N := by
  simpa only [occurrences, List.length_range] using
    (List.countP_le_length
      (p := fun n => decide (blockValue b n k = (j : ℤ))) (l := List.range N))

/-- Exact rational convergence to uniform block frequencies in an integer base.

For every positive block length `k`, every value `j < b ^ k`, and every positive
integer tolerance denominator `T`, all sufficiently large positive numbers `N`
of starting positions satisfy

`|b ^ k * occurrences b k j N - N| * T ≤ N`.

Here `Nat.dist` is the absolute difference, so natural subtraction cannot erase
a negative discrepancy.  For `N > 0`, the inequality says that the frequency
differs from `1 / b ^ k` by at most `1 / (T * b ^ k)`.  Quantifying over every
positive `T` expresses convergence without floating point arithmetic or a
chosen finite cutoff.  The threshold may depend on `k`, `j`, and `T`.

This proposition is the open research target.  No proof of `NormalInBase b` is
provided.  The finite digit certificates in this project do not establish it.
-/
def NormalInBase (b : ℕ) : Prop :=
  2 ≤ b ∧
    ∀ k : ℕ, 1 ≤ k →
      ∀ j : ℕ, j < b ^ k →
        ∀ toleranceDenominator : ℕ, 1 ≤ toleranceDenominator →
          ∃ N0 : ℕ, 1 ≤ N0 ∧
            ∀ N : ℕ, N0 ≤ N →
              Nat.dist ((b ^ k) * occurrences b k j N) N * toleranceDenominator ≤ N

end

end GoldenNormality
