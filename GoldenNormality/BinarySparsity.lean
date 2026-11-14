import FiniteMathKernels.BinaryWeight
import GoldenNormality.PowerOrbit

/-!
# An unconditional lower bound on binary one counts

Every length-`N` fractional binary prefix of the golden ratio has one count `s`
satisfying `2 * N ≤ s ^ 2 + 3 * s + 4`. The proof compares the binary weight of
a certified polynomial evaluation with the all-one block in its high bits.
The reusable binary-weight inequalities are proved in the pinned upstream
`FiniteMathKernels.BinaryWeight` module.

The certificate, whole-prefix source, and occurrence-count bridges are explicit.
This square-root-scale sparsity result does not establish simple normality or
any all-block normality estimate. The polynomial truncation method is adapted
from Bailey--Borwein--Crandall--Pomerance; no novelty claim is made here.
-/

namespace GoldenNormality

open FiniteMathKernels

/-- A binary scale cannot make the golden-ratio polynomial vanish at an integer.
The elementary obstruction is modulo three. -/
theorem binary_prefix_polynomial_ne (N q : ℕ) :
    q ^ 2 + 2 ^ N * q ≠ (2 ^ N) ^ 2 := by
  have hB : 2 ^ N % 3 ≠ 0 := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [pow_succ, Nat.mul_mod]
      have hlt : 2 ^ N % 3 < 3 := Nat.mod_lt _ (by decide)
      have hc : 2 ^ N % 3 = 1 ∨ 2 ^ N % 3 = 2 := by omega
      rcases hc with hc | hc <;> simp [hc]
  have hBlt : 2 ^ N % 3 < 3 := Nat.mod_lt _ (by decide)
  have hqlt : q % 3 < 3 := Nat.mod_lt _ (by decide)
  have hBc : 2 ^ N % 3 = 1 ∨ 2 ^ N % 3 = 2 := by omega
  have hqc : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  intro heq
  have he := congrArg (fun n : ℕ => n % 3) heq
  rw [Nat.add_mod, Nat.pow_mod q 2 3, Nat.mul_mod, Nat.pow_mod (2 ^ N) 2 3] at he
  rcases hBc with hBc | hBc <;> rcases hqc with hqc | hqc | hqc <;>
    norm_num [hBc, hqc] at he

/-- The lower endpoint of a valid binary prefix certificate is strictly below the root. -/
theorem binary_prefix_polynomial_lt {N q : ℕ}
    (certificate : PrefixCertificate (2 ^ N) q) :
    q ^ 2 + 2 ^ N * q < (2 ^ N) ^ 2 :=
  lt_of_le_of_ne certificate.1 (binary_prefix_polynomial_ne N q)

/-- For a certified prefix of at least two bits, deleting the lowest `N + 2` bits
of its polynomial evaluation leaves exactly `N - 2` consecutive one bits. -/
theorem binary_prefix_high_quotient {N q : ℕ} (hN : 2 ≤ N)
    (certificate : PrefixCertificate (2 ^ N) q) :
    (q ^ 2 + 2 ^ N * q) / 2 ^ (N + 2) = 2 ^ (N - 2) - 1 := by
  have hpos : 0 < 2 ^ N := by positivity
  have hq := certified_prefix_lt_scale hpos certificate
  have hupper := binary_prefix_polynomial_lt certificate
  have hlower : (2 ^ N) ^ 2 < q ^ 2 + 2 ^ N * q + 2 ^ (N + 2) := by
    have hc := certificate.2
    rw [pow_add]
    norm_num
    nlinarith
  have hpow : 2 ^ (N - 2) * 2 ^ (N + 2) = (2 ^ N) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    congr 1
    omega
  have hp : 1 ≤ 2 ^ (N - 2) := Nat.one_le_pow _ _ (by decide)
  have hpred : 2 ^ (N - 2) - 1 + 1 = 2 ^ (N - 2) := by omega
  have hsplit : (2 ^ (N - 2) - 1) * 2 ^ (N + 2) + 2 ^ (N + 2) =
      (2 ^ N) ^ 2 := by
    calc
      _ = (2 ^ (N - 2) - 1 + 1) * 2 ^ (N + 2) := by ring
      _ = (2 ^ N) ^ 2 := by rw [hpred, hpow]
  apply Nat.div_eq_of_lt_le
  · omega
  · rw [hpred, hpow]
    exact hupper


/-- A universal finite lower bound on the binary weight of every certified prefix.
This is a sparsity bound, not a limiting-frequency statement. -/
theorem binary_prefix_weight_bound {N q : ℕ}
    (certificate : PrefixCertificate (2 ^ N) q) :
    2 * N ≤ binaryWeight q ^ 2 + 3 * binaryWeight q + 4 := by
  by_cases hN : 2 ≤ N
  · have hlower := binaryWeight_div_two_pow_le (q ^ 2 + 2 ^ N * q) (N + 2)
    rw [binary_prefix_high_quotient hN certificate, binaryWeight_two_pow_sub_one] at hlower
    have hupper := binaryWeight_add_le (q ^ 2) (2 ^ N * q)
    rw [binaryWeight_two_pow_mul] at hupper
    have hsquare := binaryWeight_sq_le q
    have hsub : N - 2 + 2 = N := by omega
    nlinarith
  · omega

private theorem wordValue_eq_ofDigits_reverse (b : ℕ) (word : List ℕ) :
    wordValue b word = Nat.ofDigits b word.reverse := by
  induction word with
  | nil => rfl
  | cons d rest ih =>
    simp only [wordValue, Nat.ofDigits_reverse_cons, ← ih]
    ring

private theorem inAlphabet_mem_lt {b : ℕ} {word : List ℕ}
    (h : InAlphabet b word) : ∀ d ∈ word, d < b := by
  induction word with
  | nil => simp
  | cons a rest ih =>
    intro d hd
    rcases List.mem_cons.mp hd with hd | hd
    · subst d
      exact h.1
    · exact ih h.2 d hd

private theorem binary_sum_eq_ones {word : List ℕ} (h : InAlphabet 2 word) :
    word.sum = Blocks.count [1] word := by
  induction word with
  | nil => rfl
  | cons d rest ih =>
    have hd : d = 0 ∨ d = 1 := by have := h.1; omega
    rcases hd with hd | hd <;> subst d <;>
      simp [Blocks.count, Blocks.occurs, ih h.2, Nat.add_comm]

/-- For a binary word, its numeral weight is exactly its number of one symbols.
Leading zeroes are allowed; the alphabet hypothesis is retained. -/
theorem binaryWeight_wordValue {word : List ℕ} (h : InAlphabet 2 word) :
    binaryWeight (wordValue 2 word) = Blocks.count [1] word := by
  unfold binaryWeight
  rw [wordValue_eq_ofDigits_reverse]
  have hword : word.reverse ∈
      {L : List ℕ | L.length = word.length ∧ ∀ d ∈ L, d < 2} := by
    refine ⟨List.length_reverse, ?_⟩
    intro d hd
    exact inAlphabet_mem_lt h d (List.mem_reverse.mp hd)
  rw [Nat.sum_digits_ofDigits_eq_sum (by decide : 1 < 2) hword, List.sum_reverse]
  exact binary_sum_eq_ones h

/-- The total binary power evaluator produces the certified origin-prefix numeral. -/
theorem prefixCertificate_powerDigits (N : ℕ) :
    PrefixCertificate (2 ^ N) (wordValue 2 (BinaryAutomaton.powerDigits 0 N)) := by
  apply (prefixCertificate_iff_intFloor (by positivity : 0 < 2 ^ N)).mpr
  have hz : scaledFloor 2 0 = 0 := by
    simp only [scaledFloor, pow_zero, one_mul]
    exact Int.floor_eq_zero_iff.mpr ⟨le_of_lt alpha_pos, alpha_lt_one⟩
  have hv := BinaryAutomaton.wordValue_powerDigits 0 N
  simp only [blockValue, Nat.zero_add] at hv
  rw [hz, mul_zero, sub_zero] at hv
  simpa only [scaledFloor, Nat.cast_pow, Nat.cast_ofNat] using hv.symm


/-- Every origin prefix of the computable binary power orbit satisfies the bound. -/
theorem binary_power_ones_bound (N : ℕ) :
    2 * N ≤ Blocks.count [1] (BinaryAutomaton.powerDigits 0 N) ^ 2 +
      3 * Blocks.count [1] (BinaryAutomaton.powerDigits 0 N) + 4 := by
  have h := binary_prefix_weight_bound (prefixCertificate_powerDigits N)
  have ha : InAlphabet 2 (BinaryAutomaton.powerDigits 0 N) := by
    rw [BinaryAutomaton.powerDigits_eq_actualDigits]
    exact actualDigits_inAlphabet (by decide) 0 N
  rwa [binaryWeight_wordValue ha] at h

/-- The same bound concerns the actual one-digit occurrences used in normality. -/
theorem binary_occurrences_ones_bound (N : ℕ) :
    2 * N ≤ occurrences 2 1 1 N ^ 2 + 3 * occurrences 2 1 1 N + 4 := by
  have hc : Blocks.count [1] (BinaryAutomaton.powerDigits 0 N) =
      occurrences 2 1 1 N := by
    simpa [wordValue] using
      BinaryAutomaton.count_powerDigits (pattern := [1]) (by decide) (by decide) N
  simpa only [hc] using binary_power_ones_bound N

/-- A proved binary source binding beginning at zero transfers the bound to a
finite word. An arbitrary shifted segment does not satisfy this contract. -/
theorem certified_binary_ones_bound {text : List ℕ} (digits : DigitsAt 2 0 text) :
    2 * text.length ≤ Blocks.count [1] text ^ 2 + 3 * Blocks.count [1] text + 4 := by
  have he : text = BinaryAutomaton.powerDigits 0 text.length :=
    (digitsAt_eq_actualDigits digits).trans
      (BinaryAutomaton.powerDigits_eq_actualDigits 0 text.length).symm
  have h := binary_power_ones_bound text.length
  rwa [← he] at h

end GoldenNormality
