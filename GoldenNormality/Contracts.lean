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

theorem numeralBlock (b n k : ℕ) :
    (wordValue b (actualDigits b n k) : ℤ) = blockValue b n k :=
  wordValue_actualDigits b n k

theorem patternBlock (b n : ℕ) (hb : 2 ≤ b) (pattern : List ℕ)
    (ha : InAlphabet b pattern) :
    actualDigits b n pattern.length = pattern ↔
      blockValue b n pattern.length = (wordValue b pattern : ℤ) :=
  actualDigits_eq_iff_blockValue hb ha

theorem finiteFrequency (b L : ℕ) (hb : 2 ≤ b) (pattern : List ℕ)
    (hpat : pattern ≠ []) (ha : InAlphabet b pattern) :
    Blocks.count pattern (actualDigits b 0 L) =
      occurrences b pattern.length (wordValue b pattern) (L + 1 - pattern.length) :=
  count_actualDigits_eq_occurrences hb hpat ha L

theorem firstStarts (b N : ℕ) (hb : 2 ≤ b) (pattern : List ℕ)
    (hpat : pattern ≠ []) (ha : InAlphabet b pattern) :
    Blocks.count pattern (actualDigits b 0 (N + pattern.length - 1)) =
      occurrences b pattern.length (wordValue b pattern) N :=
  count_actualDigits_prefix hb hpat ha N

theorem certifiedFrequency (b value : ℕ) (hb : 2 ≤ b) (text pattern : List ℕ)
    (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) (count : Blocks.count pattern text = value) :
    occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length) =
      value :=
  certified_occurrences_sound hb hpat ha digits count

theorem certifiedDiscrepancy (b value tolerance bound : ℕ) (hb : 2 ≤ b)
    (text pattern : List ℕ) (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) (count : Blocks.count pattern text = value)
    (hbound : Nat.dist ((b ^ pattern.length) * value)
      (text.length + 1 - pattern.length) * tolerance ≤ bound) :
    Nat.dist ((b ^ pattern.length) *
      occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length))
        (text.length + 1 - pattern.length) * tolerance ≤ bound :=
  certified_discrepancy_bound hb hpat ha digits count hbound

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
