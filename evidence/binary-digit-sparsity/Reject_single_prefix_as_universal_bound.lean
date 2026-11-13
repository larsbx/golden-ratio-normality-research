import SparsityCounterexamples
open GoldenNormality FiniteMathKernels GoldenNormality.SparsityCounterexamples
example : ∀ N q : ℕ, PrefixCertificate (2 ^ N) q →
    2 * N ≤ binaryWeight q ^ 2 + 3 * binaryWeight q + 4 := firstThreeBound
