import GoldenNormality.BinarySparsity
open GoldenNormality FiniteMathKernels
example (N q : ℕ) (h : PrefixCertificate (3 ^ N) q) :
    2 * N ≤ binaryWeight q ^ 2 + 3 * binaryWeight q + 4 :=
  binary_prefix_weight_bound h
