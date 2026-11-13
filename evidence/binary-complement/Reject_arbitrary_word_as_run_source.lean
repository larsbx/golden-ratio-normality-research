import GoldenNormality.BinaryRuns
open GoldenNormality
example (start length d : ℕ) (text : List ℕ)
    (run : text = List.replicate length d) : length ≤ start + 1 :=
  certified_binary_constant_run_bound run
