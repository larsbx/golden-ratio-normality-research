import GoldenNormality

/-!
Exact public contract checks. These explicit types prevent a successful build
of a weaker, differently quantified theorem from satisfying the acceptance gate.
The gate also inspects the compiled declarations and their transitive axioms.
-/

namespace GoldenNormality.Contracts

theorem root (B q : ℕ) (hB : 0 < B) :
    PrefixCertificate B q ↔ Int.floor ((B : ℝ) * alpha) = (q : ℤ) :=
  prefixCertificate_iff_intFloor hB

theorem adjacentPrefixes (b n q r : ℕ) (hb : 2 ≤ b)
    (hq : PrefixCertificate (b ^ n) q) (hr : PrefixCertificate (b ^ (n + 1)) r) :
    digit b n = (r : ℤ) - (b : ℤ) * q := digit_of_certificates hb hq hr

theorem blockSemantics (b n k : ℕ) :
    blockValue b n k = Int.floor ((b : ℝ) ^ k * Int.fract ((b : ℝ) ^ n * alpha)) :=
  blockValue_eq_floor_fract b n k

theorem consecutiveCount (pattern text : List ℕ) :
    Blocks.count pattern text = Blocks.enumeratedCount pattern text :=
  Blocks.count_eq_enumerated pattern text

theorem chunkBoundary (pattern left right : List ℕ) :
    Blocks.count pattern (left ++ right) =
      Blocks.count pattern left + Blocks.count pattern right +
        Blocks.boundaryCount pattern left right :=
  Blocks.count_append_boundary pattern left right

theorem automatonLanguage (digits : List Bool) :
    BinaryAutomaton.classify digits ≠ none ↔ BinaryAutomaton.Admissible digits :=
  BinaryAutomaton.classify_accepts_iff digits

theorem automatonAllInputs (digits : List Bool) (d : ℕ)
    (h : BinaryAutomaton.classify digits = some d) :
    BinaryAutomaton.binaryDifference (BinaryAutomaton.fibonacciSum digits 2) = (d : ℤ) :=
  BinaryAutomaton.classify_correct h

theorem automatonPowerInput (digits : List Bool) (n d : ℕ)
    (hv : BinaryAutomaton.fibonacciSum digits 2 = 2 ^ n)
    (ho : BinaryAutomaton.classify digits = some d) :
    digit 2 n = (d : ℤ) := BinaryAutomaton.power_input_digit hv ho

end GoldenNormality.Contracts
