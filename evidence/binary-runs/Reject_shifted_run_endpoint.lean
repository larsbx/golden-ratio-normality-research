import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length q r : ℕ)
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length + 1)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_zero_run_bound lower upper run
