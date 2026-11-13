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

theorem fixedWidthCoverage (b k j : ℕ) (hb : 2 ≤ b) (hj : j < b ^ k) :
    ∃! word : List ℕ, word.length = k ∧ InAlphabet b word ∧ wordValue b word = j :=
  existsUnique_wordValue hb hj

theorem wordRoundTrip (b : ℕ) (hb : 2 ≤ b) (word : List ℕ) (ha : InAlphabet b word) :
    wordOfValue b word.length (wordValue b word) = word :=
  wordOfValue_wordValue hb ha

theorem normalityWords (b : ℕ) :
    NormalInBase b ↔
      (2 ≤ b ∧ ∀ pattern : List ℕ, pattern ≠ [] → InAlphabet b pattern →
        ∀ T : ℕ, 1 ≤ T → ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
          Nat.dist ((b ^ pattern.length) *
            Blocks.count pattern (actualDigits b 0 (N + pattern.length - 1))) N * T ≤ N) :=
  normalInBase_iff_normalByWords b

theorem normalityUniformValues (b : ℕ) :
    NormalInBase b ↔
      (2 ≤ b ∧ ∀ k : ℕ, 1 ≤ k → ∀ T : ℕ, 1 ≤ T →
        ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ j : ℕ, j < b ^ k →
          Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N) :=
  normalInBase_iff_uniformBlockNormality b

theorem checkpointInterpolation (b k j L N R : ℕ) (hLN : L ≤ N) (hNR : N ≤ R) :
    Nat.dist ((b ^ k) * occurrences b k j N) N ≤
      max (Nat.dist ((b ^ k) * occurrences b k j L) L)
        (Nat.dist ((b ^ k) * occurrences b k j R) R) + (R - L) :=
  occurrences_discrepancy_interpolation b k j L N R hLN hNR

theorem certifiedInterval (b lowerCount upperCount N T : ℕ) (hb : 2 ≤ b)
    (lowerText upperText pattern : List ℕ) (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (lowerDigits : DigitsAt b 0 lowerText) (upperDigits : DigitsAt b 0 upperText)
    (lowerExact : Blocks.count pattern lowerText = lowerCount)
    (upperExact : Blocks.count pattern upperText = upperCount)
    (hLN : lowerText.length + 1 - pattern.length ≤ N)
    (hNR : N ≤ upperText.length + 1 - pattern.length)
    (budget :
      (max (Nat.dist ((b ^ pattern.length) * lowerCount)
          (lowerText.length + 1 - pattern.length))
        (Nat.dist ((b ^ pattern.length) * upperCount)
          (upperText.length + 1 - pattern.length)) +
        ((upperText.length + 1 - pattern.length) -
          (lowerText.length + 1 - pattern.length))) * T ≤
        lowerText.length + 1 - pattern.length) :
    Nat.dist ((b ^ pattern.length) *
      occurrences b pattern.length (wordValue b pattern) N) N * T ≤ N :=
  certified_interval_bound hb hpat ha lowerDigits upperDigits lowerExact upperExact hLN hNR budget

theorem checkpointCoverage (q : ℕ → ℕ) (hq : StrictMono q) (i0 N : ℕ) (hstart : q i0 ≤ N) :
    ∃ i : ℕ, i0 ≤ i ∧ q i ≤ N ∧ N ≤ q (i + 1) :=
  checkpoint_interval_covers hq i0 N hstart

theorem checkpointNormality (b : ℕ) (hb : 2 ≤ b)
    (checkpoints : ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j < b ^ k → ∀ T : ℕ, 1 ≤ T →
      ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
        (max (Nat.dist ((b ^ k) * occurrences b k j (q i)) (q i))
          (Nat.dist ((b ^ k) * occurrences b k j (q (i + 1))) (q (i + 1))) +
          (q (i + 1) - q i)) * T ≤ q i) :
    NormalInBase b :=
  normalInBase_of_checkpoint_bounds hb checkpoints

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

theorem fibonacciEncoding (q : ℕ) :
    BinaryAutomaton.Admissible (BinaryAutomaton.encode q) ∧
      BinaryAutomaton.fibonacciSum (BinaryAutomaton.encode q) 2 = q :=
  ⟨BinaryAutomaton.encode_admissible q, BinaryAutomaton.fibonacciSum_encode q⟩

theorem automatonEvaluation (q : ℕ) :
    BinaryAutomaton.classify (BinaryAutomaton.encode q) = some (BinaryAutomaton.evaluated q) ∧
      BinaryAutomaton.evaluated q < 2 ∧
        BinaryAutomaton.binaryDifference q = (BinaryAutomaton.evaluated q : ℤ) :=
  ⟨BinaryAutomaton.classify_encode q, BinaryAutomaton.evaluated_lt_two q,
    BinaryAutomaton.evaluated_correct q⟩

theorem binaryPowerDigit (n : ℕ) : digit 2 n = (BinaryAutomaton.powerDigit n : ℤ) :=
  BinaryAutomaton.powerDigit_correct n

theorem binaryPowerWord (start length : ℕ) :
    DigitsAt 2 start (BinaryAutomaton.powerDigits start length) ∧
      (BinaryAutomaton.powerDigits start length).length = length ∧
        (wordValue 2 (BinaryAutomaton.powerDigits start length) : ℤ) =
          blockValue 2 start length :=
  ⟨BinaryAutomaton.powerDigits_digitsAt start length,
    BinaryAutomaton.powerDigits_length start length,
    BinaryAutomaton.wordValue_powerDigits start length⟩

theorem binaryPowerFrequency (pattern : List ℕ) (N : ℕ)
    (hpat : pattern ≠ []) (ha : InAlphabet 2 pattern) :
    Blocks.count pattern (BinaryAutomaton.powerDigits 0 (N + pattern.length - 1)) =
      occurrences 2 pattern.length (wordValue 2 pattern) N :=
  BinaryAutomaton.count_powerDigits hpat ha N

theorem binaryPowerNormality :
    (∀ pattern : List ℕ, pattern ≠ [] → InAlphabet 2 pattern →
      ∀ T : ℕ, 1 ≤ T → ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
        Nat.dist ((2 ^ pattern.length) *
          Blocks.count pattern (BinaryAutomaton.powerDigits 0 (N + pattern.length - 1))) N * T ≤ N)
      ↔ NormalInBase 2 :=
  BinaryAutomaton.powerOrbitNormality_iff_normalInBase

theorem certifiedPowerSource (start : ℕ) (inputs : List (List Bool)) (outputs : List ℕ)
    (orbit : BinaryAutomaton.PowerOrbitAt start inputs outputs) :
    inputs.length = outputs.length ∧ DigitsAt 2 start outputs ∧
      outputs = BinaryAutomaton.powerDigits start outputs.length :=
  ⟨BinaryAutomaton.powerOrbitAt_length orbit, BinaryAutomaton.powerOrbitAt_digitsAt orbit,
    BinaryAutomaton.powerOrbitAt_eq_powerDigits orbit⟩

theorem certifiedPowerFrequency (value : ℕ) (inputs : List (List Bool))
    (outputs pattern : List ℕ) (hpat : pattern ≠ []) (ha : InAlphabet 2 pattern)
    (orbit : BinaryAutomaton.PowerOrbitAt 0 inputs outputs)
    (count : Blocks.count pattern outputs = value) :
    occurrences 2 pattern.length (wordValue 2 pattern)
      (outputs.length + 1 - pattern.length) = value :=
  BinaryAutomaton.certified_power_occurrences hpat ha orbit count

theorem endpointBudget (L R lowerError upperError T : ℕ)
    (hLR : L ≤ R) (hT : 1 ≤ T)
    (lower : lowerError * (4 * T) ≤ L)
    (upper : upperError * (4 * T) ≤ R)
    (gap : (R - L) * (4 * T) ≤ L) :
    (max lowerError upperError + (R - L)) * T ≤ L :=
  checkpoint_budget_of_endpoint_bounds L R lowerError upperError T hLR hT lower upper gap

theorem endpointInterpolation (b k j L N R T : ℕ)
    (hT : 1 ≤ T) (hLN : L ≤ N) (hNR : N ≤ R)
    (lower : Nat.dist ((b ^ k) * occurrences b k j L) L * (4 * T) ≤ L)
    (upper : Nat.dist ((b ^ k) * occurrences b k j R) R * (4 * T) ≤ R)
    (gap : (R - L) * (4 * T) ≤ L) :
    Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N :=
  occurrences_interval_bound_of_endpoint_bounds b k j L N R T hT hLN hNR lower upper gap

theorem sparseCheckpointNormality (b : ℕ) (q : ℕ → ℕ) (hq : StrictMono q)
    (hgaps : ∀ T : ℕ, 1 ≤ T →
      ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i → (q (i + 1) - q i) * T ≤ q i) :
    NormalInBase b ↔
      (2 ≤ b ∧ ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j < b ^ k →
        ∀ T : ℕ, 1 ≤ T → ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
          Nat.dist ((b ^ k) * occurrences b k j (q i)) (q i) * T ≤ q i) :=
  normalInBase_iff_normalOnCheckpoints b hq hgaps

theorem squareGeometry :
    StrictMono squareCheckpoint ∧
      (∀ i : ℕ, squareCheckpoint (i + 1) - squareCheckpoint i = 2 * i + 1) ∧
      (∀ i T : ℕ, 1 ≤ T → 3 * T ≤ i →
        (squareCheckpoint (i + 1) - squareCheckpoint i) * T ≤ squareCheckpoint i) :=
  ⟨squareCheckpoint_strictMono, squareCheckpoint_gap,
    fun _ _ hT hi => squareCheckpoint_gap_bound hT hi⟩

theorem squareCheckpointNormality (b : ℕ) :
    NormalInBase b ↔
      (2 ≤ b ∧ ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j < b ^ k →
        ∀ T : ℕ, 1 ≤ T → ∃ i0 : ℕ, ∀ i : ℕ, i0 ≤ i →
          Nat.dist ((b ^ k) * occurrences b k j (i ^ 2)) (i ^ 2) * T ≤ i ^ 2) :=
  normalInBase_iff_squareCheckpoints b

theorem squareInterval (b k j i N T : ℕ)
    (hT : 1 ≤ T) (hi : 12 * T ≤ i)
    (hLN : i ^ 2 ≤ N) (hNR : N ≤ (i + 1) ^ 2)
    (lower : Nat.dist ((b ^ k) * occurrences b k j (i ^ 2)) (i ^ 2) * (4 * T) ≤ i ^ 2)
    (upper : Nat.dist ((b ^ k) * occurrences b k j ((i + 1) ^ 2)) ((i + 1) ^ 2) *
      (4 * T) ≤ (i + 1) ^ 2) :
    Nat.dist ((b ^ k) * occurrences b k j N) N * T ≤ N :=
  occurrences_square_interval_bound b k j i N T hT hi hLN hNR lower upper

theorem binarySquareNormality :
    (∀ pattern : List ℕ, pattern ≠ [] → InAlphabet 2 pattern →
      ∀ T : ℕ, 1 ≤ T → ∃ i0 : ℕ, 1 ≤ i0 ∧ ∀ i : ℕ, i0 ≤ i →
        Nat.dist ((2 ^ pattern.length) *
          Blocks.count pattern (BinaryAutomaton.powerDigits 0 (i ^ 2 + pattern.length - 1)))
          (i ^ 2) * T ≤ i ^ 2) ↔ NormalInBase 2 :=
  BinaryAutomaton.powerOrbitSquareNormality_iff_normalInBase

theorem binaryPrefixSparsity (N q : ℕ) (certificate : PrefixCertificate (2 ^ N) q) :
    2 * N ≤ FiniteMathKernels.binaryWeight q ^ 2 + 3 * FiniteMathKernels.binaryWeight q + 4 :=
  binary_prefix_weight_bound certificate

theorem binaryPrefixHighBits (N q : ℕ) (hN : 2 ≤ N)
    (certificate : PrefixCertificate (2 ^ N) q) :
    (q ^ 2 + 2 ^ N * q) / 2 ^ (N + 2) = 2 ^ (N - 2) - 1 :=
  binary_prefix_high_quotient hN certificate

theorem binaryWordOnes (word : List ℕ) (alphabet : InAlphabet 2 word) :
    FiniteMathKernels.binaryWeight (wordValue 2 word) = Blocks.count [1] word :=
  binaryWeight_wordValue alphabet

theorem binaryPowerPrefix (N : ℕ) :
    PrefixCertificate (2 ^ N) (wordValue 2 (BinaryAutomaton.powerDigits 0 N)) :=
  prefixCertificate_powerDigits N

theorem binaryPowerOnes (N : ℕ) :
    2 * N ≤ Blocks.count [1] (BinaryAutomaton.powerDigits 0 N) ^ 2 +
      3 * Blocks.count [1] (BinaryAutomaton.powerDigits 0 N) + 4 :=
  binary_power_ones_bound N

theorem binaryOccurrencesOnes (N : ℕ) :
    2 * N ≤ occurrences 2 1 1 N ^ 2 + 3 * occurrences 2 1 1 N + 4 :=
  binary_occurrences_ones_bound N

theorem certifiedBinaryOnes (word : List ℕ) (digits : DigitsAt 2 0 word) :
    2 * word.length ≤ Blocks.count [1] word ^ 2 + 3 * Blocks.count [1] word + 4 :=
  certified_binary_ones_bound digits

theorem binaryZeroRun (start length q r : ℕ)
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r = 2 ^ length * q) : length ≤ start + 1 :=
  binary_zero_run_bound lower upper run

theorem binaryOneRun (start length q r : ℕ)
    (lower : PrefixCertificate (2 ^ start) q)
    (upper : PrefixCertificate (2 ^ (start + length)) r)
    (run : r + 1 = 2 ^ length * (q + 1)) : length ≤ start + 1 :=
  binary_one_run_bound lower upper run

theorem binaryPowerConstantRun (start length d : ℕ)
    (run : BinaryAutomaton.powerDigits start length = List.replicate length d) :
    length ≤ start + 1 :=
  binary_power_constant_run_bound run

theorem binaryActualConstantRun (start length d : ℕ)
    (run : actualDigits 2 start length = List.replicate length d) :
    length ≤ start + 1 :=
  binary_actual_constant_run_bound run

theorem certifiedBinaryConstantRun (start length d : ℕ)
    (digits : DigitsAt 2 start (List.replicate length d)) : length ≤ start + 1 :=
  certified_binary_constant_run_bound digits

theorem binaryWindowSymbols (start d : ℕ) (hd : d < 2) :
    d ∈ actualDigits 2 start (start + 2) :=
  binary_actual_window_contains start d hd

theorem binaryPowerWindowSymbols (start d : ℕ) (hd : d < 2) :
    d ∈ BinaryAutomaton.powerDigits start (start + 2) :=
  binary_power_window_contains start d hd

theorem binarySymbolCountGrowth (start d : ℕ) (hd : d < 2) :
    Blocks.count [d] (BinaryAutomaton.powerDigits 0 start) + 1 ≤
      Blocks.count [d] (BinaryAutomaton.powerDigits 0 (2 * start + 2)) :=
  binary_power_count_growth start d hd

theorem binaryLogarithmicCounts (m d : ℕ) (hd : d < 2) :
    m ≤ occurrences 2 1 d (2 ^ (m + 1) - 2) :=
  binary_occurrences_logarithmic_bound m d hd

theorem binaryLaterCounts (m d N : ℕ) (hd : d < 2)
    (hN : 2 ^ (m + 1) - 2 ≤ N) : m ≤ occurrences 2 1 d N :=
  binary_occurrences_at_least m d N hd hN

theorem binaryCountPartition (N : ℕ) :
    occurrences 2 1 0 N + occurrences 2 1 1 N = N :=
  binary_occurrences_partition N

theorem binaryTwoSidedCounts (m N : ℕ) (hN : 2 ^ (m + 1) - 2 ≤ N) :
    m ≤ occurrences 2 1 1 N ∧ occurrences 2 1 1 N + m ≤ N :=
  binary_occurrences_two_sided m N hN

theorem binaryDigitRecurrence (start d : ℕ) (hd : d < 2) :
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ digit 2 n = (d : ℤ) :=
  binary_digit_symbol_recurs start d hd

theorem binaryNoConstantTail :
    ¬ ∃ start : ℕ, ∃ d : ℤ, ∀ n : ℕ, start ≤ n → digit 2 n = d :=
  binary_digit_not_eventually_constant

end GoldenNormality.Contracts
