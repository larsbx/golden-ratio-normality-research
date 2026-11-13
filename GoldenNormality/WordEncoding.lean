import GoldenNormality.BlockNumerals

/-!
# Canonical words of a fixed width

`wordOfValue b k j` is a computable most-significant-digit-first decoder with
exactly `k` symbols.  For `2 ≤ b` and `j < b^k`, it is the unique alphabet word
of that length and value.  Leading zeroes are retained.  Width zero is included:
its permitted value is zero, represented by the empty word.
-/

namespace GoldenNormality

/-- Decode a value into exactly the requested number of most-significant-first symbols. -/
def wordOfValue (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, j => j / b ^ k :: wordOfValue b k (j % b ^ k)

@[simp] theorem wordOfValue_zero (b j : ℕ) : wordOfValue b 0 j = [] := rfl

theorem wordOfValue_succ (b k j : ℕ) :
    wordOfValue b (k + 1) j = j / b ^ k :: wordOfValue b k (j % b ^ k) := rfl

/-- The width is preserved for every input, independently of the value bound. -/
@[simp] theorem wordOfValue_length (b k j : ℕ) : (wordOfValue b k j).length = k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih => simp only [wordOfValue, List.length_cons, ih]

/-- Decoding a value below `b^k` produces symbols in the base-`b` alphabet. -/
theorem wordOfValue_inAlphabet {b k j : ℕ} (hb : 2 ≤ b) (hj : j < b ^ k) :
    InAlphabet b (wordOfValue b k j) := by
  have hbpos : 0 < b := by omega
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    constructor
    · exact Nat.div_lt_of_lt_mul (by simpa only [pow_succ] using hj)
    · exact ih (Nat.mod_lt j (pow_pos hbpos k))

/-- Evaluating the canonical word recovers every value in the prescribed range. -/
theorem wordValue_wordOfValue {b k j : ℕ} (hb : 2 ≤ b) (hj : j < b ^ k) :
    wordValue b (wordOfValue b k j) = j := by
  have hbpos : 0 < b := by omega
  induction k generalizing j with
  | zero =>
    have hjzero : j = 0 := by simpa using hj
    subst j
    rfl
  | succ k ih =>
    simp only [wordOfValue, wordValue, wordOfValue_length]
    rw [ih (Nat.mod_lt j (pow_pos hbpos k))]
    exact Nat.div_add_mod' j (b ^ k)

/-- Encoding and decoding an alphabet word preserves its full width and symbols. -/
theorem wordOfValue_wordValue {b : ℕ} (hb : 2 ≤ b) {word : List ℕ}
    (hw : InAlphabet b word) :
    wordOfValue b word.length (wordValue b word) = word := by
  exact wordValue_injective (wordOfValue_inAlphabet hb (wordValue_lt hw)) hw
    (wordOfValue_length b word.length (wordValue b word))
    (wordValue_wordOfValue hb (wordValue_lt hw))

/-- Every block value has an alphabet word of exactly its specified width. -/
theorem exists_word_of_lt {b k j : ℕ} (hb : 2 ≤ b) (hj : j < b ^ k) :
    ∃ word : List ℕ, InAlphabet b word ∧ word.length = k ∧ wordValue b word = j := by
  exact ⟨wordOfValue b k j, wordOfValue_inAlphabet hb hj,
    wordOfValue_length b k j, wordValue_wordOfValue hb hj⟩

/-- Each value below `b^k` has exactly one alphabet representation of width `k`. -/
theorem existsUnique_wordValue {b k j : ℕ} (hb : 2 ≤ b) (hj : j < b ^ k) :
    ∃! word : List ℕ, word.length = k ∧ InAlphabet b word ∧ wordValue b word = j := by
  refine ⟨wordOfValue b k j, ?_, ?_⟩
  · exact ⟨wordOfValue_length b k j, wordOfValue_inAlphabet hb hj,
      wordValue_wordOfValue hb hj⟩
  · intro word hw
    calc
      word = wordOfValue b word.length (wordValue b word) :=
        (wordOfValue_wordValue hb hw.2.1).symm
      _ = wordOfValue b k j := by rw [hw.1, hw.2.2]

end GoldenNormality
