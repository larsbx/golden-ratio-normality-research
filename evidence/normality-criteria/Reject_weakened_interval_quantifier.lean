import Receipts
open GoldenNormality
namespace WeakenedIntervalControl
theorem endpointOnly : Nat.dist (2 ^ 3 * occurrences 2 3 0 222) 222 * 2 ≤ 222 :=
  Receipts.interval_0_0 222 (by decide) (by decide)
example : ∀ N : ℕ, 222 ≤ N → N ≤ 254 →
    Nat.dist (2 ^ 3 * occurrences 2 3 0 N) N * 2 ≤ N :=
  endpointOnly
end WeakenedIntervalControl
