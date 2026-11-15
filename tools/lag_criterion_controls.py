"""Reject weakening the spacing and all-differences hypotheses."""

REJECTIONS = {
    "lag_criterion_without_positive_spacing": ("""import GoldenNormality
open GoldenNormality GoldenNormality.BinaryDyadicOrbit

example (spacing : ℤ → ℕ) (h : ∀ k : ℤ, k % 2 = 1 → 0 ≤ spacing k) :
    NormalInBase 2 ↔ ∀ k : ℤ, k % 2 = 1 → LagUpperZero k (spacing k) :=
  normalInBase_iff_spaced_lag_upper spacing h
""", r"[Aa]pplication type mismatch"),
    "lag_criterion_only_one_difference": ("""import GoldenNormality
open GoldenNormality.BinaryDyadicOrbit Filter
open scoped Topology

example (h : ℤ) (L : ℕ)
    (one : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (dyadicModularAverage (lagFrequency h L 1) N).re ≤ ε) :
    Tendsto (dyadicModularAverage h) atTop (𝓝 0) :=
  tendsto_dyadicModularAverage_of_lagUpperZero h L one
""", r"[Aa]pplication type mismatch"),
}
