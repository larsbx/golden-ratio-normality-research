import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length q r : ℕ)
    (lower : q ^ 2 + 2 ^ start * q ≤ (2 ^ start) ^ 2)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_zero_run_bound lower upper run
