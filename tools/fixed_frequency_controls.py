"""Reject two extensions of the frequency-one deficit contract."""

REJECTIONS = {
    "fixed_frequency_without_width_bound": ("""import GoldenNormality
open GoldenNormality.BinaryDyadicOrbit

example (k N : ℕ) (h : k ≤ N) :
    (N : ℝ) * ‖dyadicModularAverage 1 N‖ +
      (1 - Real.sqrt 2 / 2) * (k : ℝ) ≤ (N : ℝ) :=
  norm_dyadicModularAverage_one_mul_add_log_le k N h
""", r"[Aa]pplication type mismatch"),
    "fixed_frequency_relabelled_mode": ("""import GoldenNormality
open GoldenNormality.BinaryDyadicOrbit

example (k N : ℕ) (h : 2 ^ k ≤ N) :
    (N : ℝ) * ‖dyadicModularAverage 3 N‖ +
      (1 - Real.sqrt 2 / 2) * (k : ℝ) ≤ (N : ℝ) :=
  norm_dyadicModularAverage_one_mul_add_log_le k N h
""", r"[Tt]ype mismatch"),
}
