import GoldenNormality.BinarySparsity
open GoldenNormality FiniteMathKernels
example (N q : ℕ) (h : q ^ 2 + 2 ^ N * q ≤ (2 ^ N) ^ 2) :
    2 * N ≤ binaryWeight q ^ 2 + 3 * binaryWeight q + 4 :=
  binary_prefix_weight_bound h
