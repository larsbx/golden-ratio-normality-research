import GoldenNormality.BinaryRuns
import GoldenNormality.CheckpointBounds

/-!
# Quantitative recurrence of both binary symbols

The preceding run bound places each binary symbol in every window starting at
`n` of length `n + 2`. Disjoint windows with endpoints `2^(m+1)-2` therefore
give at least `m` occurrences of each symbol in that origin prefix. These are
explicit logarithmic-scale count bounds and recurrence bounds at every start.
They do not give positive density, frequency one half, or normality.
-/

namespace GoldenNormality
open BinaryAutomaton

private theorem powerDigits_append (start left right : ℕ) :
    powerDigits start (left + right) =
      powerDigits start left ++ powerDigits (start + left) right := by
  induction left generalizing start with
  | zero => simp
  | succ left ih =>
    rw [show left + 1 + right = (left + right) + 1 by omega,
      powerDigits_succ, powerDigits_succ, ih, List.cons_append]
    rw [show start + 1 + left = start + (left + 1) by omega]

private theorem singleton_count_pos_of_mem {d : ℕ} {text : List ℕ}
    (h : d ∈ text) : 0 < Blocks.count [d] text := by
  induction text with
  | nil => simp at h
  | cons a text ih =>
    rcases List.mem_cons.mp h with h | h
    · subst a
      simp [Blocks.count, Blocks.occurs]
    · have ht := ih h
      simp only [Blocks.count]
      omega

private theorem powerDigits_mem_iff (start length d : ℕ) :
    d ∈ powerDigits start length ↔
      ∃ n : ℕ, start ≤ n ∧ n < start + length ∧ powerDigit n = d := by
  induction length generalizing start with
  | zero =>
    simp only [powerDigits_zero, List.not_mem_nil, Nat.add_zero]
    constructor
    · exact False.elim
    · rintro ⟨n, hn, hlast, _⟩
      omega
  | succ length ih =>
    rw [powerDigits_succ, List.mem_cons, ih]
    constructor
    · rintro (he | ⟨n, hn, hlast, hd⟩)
      · exact ⟨start, by omega, by omega, he.symm⟩
      · exact ⟨n, by omega, by omega, hd⟩
    · rintro ⟨n, hn, hlast, hd⟩
      by_cases he : n = start
      · left
        subst n
        exact hd.symm
      · right
        exact ⟨n, by omega, by omega, hd⟩

private theorem count_growth_from_member (start d : ℕ)
    (h : d ∈ powerDigits start (start + 2)) :
    Blocks.count [d] (powerDigits 0 start) + 1 ≤
      Blocks.count [d] (powerDigits 0 (2 * start + 2)) := by
  have he : 2 * start + 2 = start + (start + 2) := by omega
  rw [he, powerDigits_append, Nat.zero_add, Blocks.count_append]
  have hpos := singleton_count_pos_of_mem h
  omega

private theorem checkpoint_succ (m : ℕ) :
    2 ^ ((m + 1) + 1) - 2 = 2 * (2 ^ (m + 1) - 2) + 2 := by
  have hpow : 2 ≤ 2 ^ (m + 1) := by
    rw [pow_succ]
    have hone : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by decide)
    omega
  rw [pow_succ]
  omega

/-- Each guaranteed window adds at least one occurrence of either binary symbol. -/
theorem binary_power_count_growth (start d : ℕ) (hd : d < 2) :
    Blocks.count [d] (powerDigits 0 start) + 1 ≤
      Blocks.count [d] (powerDigits 0 (2 * start + 2)) :=
  count_growth_from_member start d (binary_power_window_contains start d hd)

/-- The first `2^(m+1)-2` binary digits contain at least `m` copies of each
binary symbol. The exponentially spaced disjoint windows provide an explicit
logarithmic-scale bound, not a positive-density assertion. -/
theorem binary_occurrences_logarithmic_bound (m d : ℕ) (hd : d < 2) :
    m ≤ occurrences 2 1 d (2 ^ (m + 1) - 2) := by
  have hcount : m ≤ Blocks.count [d] (powerDigits 0 (2 ^ (m + 1) - 2)) := by
    induction m with
    | zero => exact Nat.zero_le _
    | succ m ih =>
      have hg := binary_power_count_growth (2 ^ (m + 1) - 2) d hd
      rw [checkpoint_succ]
      omega
  have hc := count_powerDigits (pattern := [d]) (by simp) (by simpa using hd)
    (2 ^ (m + 1) - 2)
  simpa [wordValue] using hcount.trans_eq hc

/-- The explicit symbol-count threshold applies to every later prefix. -/
theorem binary_occurrences_at_least (m d N : ℕ) (hd : d < 2)
    (hN : 2 ^ (m + 1) - 2 ≤ N) : m ≤ occurrences 2 1 d N :=
  (binary_occurrences_logarithmic_bound m d hd).trans
    (occurrences_monotone 2 1 d hN)

private theorem binary_word_partition {text : List ℕ} (ha : InAlphabet 2 text) :
    Blocks.count [0] text + Blocks.count [1] text = text.length := by
  induction text with
  | nil => rfl
  | cons a text ih =>
    have ha01 : a = 0 ∨ a = 1 := by have := ha.1; omega
    have ht := ih ha.2
    rcases ha01 with ha0 | ha1 <;> subst a <;>
      simp [Blocks.count, Blocks.occurs, Nat.add_comm] at * <;> omega

/-- Zero and one counts partition every binary origin prefix exactly. -/
theorem binary_occurrences_partition (N : ℕ) :
    occurrences 2 1 0 N + occurrences 2 1 1 N = N := by
  have ha : InAlphabet 2 (powerDigits 0 N) := by
    rw [powerDigits_eq_actualDigits]
    exact actualDigits_inAlphabet (by decide) 0 N
  have h := binary_word_partition ha
  have h0 : Blocks.count [0] (powerDigits 0 N) = occurrences 2 1 0 N := by
    simpa [wordValue] using
      count_powerDigits (pattern := [0]) (by decide) (by decide) N
  have h1 : Blocks.count [1] (powerDigits 0 N) = occurrences 2 1 1 N := by
    simpa [wordValue] using
      count_powerDigits (pattern := [1]) (by decide) (by decide) N
  simpa only [h0, h1, powerDigits_length] using h

/-- Past the explicit threshold, neither binary symbol can leave fewer than
`m` copies of the other symbol in the observed prefix. -/
theorem binary_occurrences_two_sided (m N : ℕ)
    (hN : 2 ^ (m + 1) - 2 ≤ N) :
    m ≤ occurrences 2 1 1 N ∧ occurrences 2 1 1 N + m ≤ N := by
  have h0 := binary_occurrences_at_least m 0 N (by decide) hN
  have h1 := binary_occurrences_at_least m 1 N (by decide) hN
  have hp := binary_occurrences_partition N
  omega

/-- Each binary symbol recurs at a source position in the stated half-open
interval; the upper endpoint is excluded. -/
theorem binary_power_symbol_recurs (start d : ℕ) (hd : d < 2) :
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ powerDigit n = d := by
  obtain ⟨n, hn, hlast, hdigit⟩ :=
    (powerDigits_mem_iff start (start + 2) d).mp
      (binary_power_window_contains start d hd)
  exact ⟨n, hn, by omega, hdigit⟩

/-- Quantitative recurrence in the actual golden-ratio fractional digits. -/
theorem binary_digit_symbol_recurs (start d : ℕ) (hd : d < 2) :
    ∃ n : ℕ, start ≤ n ∧ n < 2 * start + 2 ∧ digit 2 n = (d : ℤ) := by
  obtain ⟨n, hn, hlast, hdigit⟩ := binary_power_symbol_recurs start d hd
  exact ⟨n, hn, hlast, by rw [powerDigit_correct, hdigit]⟩

/-- The computable binary output sequence has no eventually constant tail. -/
theorem binary_power_not_eventually_constant :
    ¬ ∃ start d : ℕ, ∀ n : ℕ, start ≤ n → powerDigit n = d := by
  rintro ⟨start, d, h⟩
  obtain ⟨n, hn, _, hn0⟩ := binary_power_symbol_recurs start 0 (by decide)
  obtain ⟨m, hm, _, hm1⟩ := binary_power_symbol_recurs start 1 (by decide)
  have h0 := h n hn
  have h1 := h m hm
  omega

/-- Neither termination in zeros nor an eventual all-one tail is possible for
the actual binary expansion. This does not assert nonperiodicity of every period. -/
theorem binary_digit_not_eventually_constant :
    ¬ ∃ start : ℕ, ∃ d : ℤ, ∀ n : ℕ, start ≤ n → digit 2 n = d := by
  rintro ⟨start, d, h⟩
  obtain ⟨n, hn, _, hn0⟩ := binary_digit_symbol_recurs start 0 (by decide)
  obtain ⟨m, hm, _, hm1⟩ := binary_digit_symbol_recurs start 1 (by decide)
  have h0 := h n hn
  have h1 := h m hm
  omega

end GoldenNormality
