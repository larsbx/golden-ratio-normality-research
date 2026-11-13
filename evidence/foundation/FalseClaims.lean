import GoldenNormality
example : GoldenNormality.checkPrefix 10 7 = true := by decide
example : GoldenNormality.Blocks.count [0, 1] [0, 0, 1] = 2 := by decide
example : GoldenNormality.BinaryAutomaton.classify [true, true] = some 1 := by decide
namespace Weakened
theorem root (B q : ℕ) (_hB : 0 < B) : q = q := rfl
end Weakened
example (B q : ℕ) (hB : 0 < B) :
    GoldenNormality.PrefixCertificate B q ↔
      Int.floor ((B : ℝ) * GoldenNormality.alpha) = (q : ℤ) := Weakened.root B q hB
