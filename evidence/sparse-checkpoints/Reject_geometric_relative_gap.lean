import CheckpointCounterexamples
open GoldenNormality.CheckpointCounterexamples
example : (geometricCheckpoint (4 + 1) - geometricCheckpoint 4) * 2 ≤
    geometricCheckpoint 4 := by decide
