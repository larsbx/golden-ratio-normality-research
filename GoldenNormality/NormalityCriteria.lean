import GoldenNormality.WordEncoding
import GoldenNormality.FrequencyBridge

/-!
# Equivalent normality criteria

The existing open target can be stated using complete finite digit words, with
the same block length, tolerance, positive threshold, and all subsequent starts.
For a fixed block length and tolerance, finitely many value-specific thresholds
can also be replaced by their maximum. This does not provide a threshold shared
by different block lengths or tolerances, nor prove any normality target.
-/

namespace GoldenNormality

/-- The normality target expressed using nonempty alphabet words and their
exact overlapping counts in prefixes containing the first `N` complete starts.
The threshold may depend on the whole pattern and the tolerance denominator.
-/
def NormalByWords (b : ℕ) : Prop :=
  2 ≤ b ∧
    ∀ pattern : List ℕ, pattern ≠ [] → InAlphabet b pattern →
      ∀ toleranceDenominator : ℕ, 1 ≤ toleranceDenominator →
        ∃ N0 : ℕ, 1 ≤ N0 ∧
          ∀ N : ℕ, N0 ≤ N →
            Nat.dist ((b ^ pattern.length) *
              Blocks.count pattern (actualDigits b 0 (N + pattern.length - 1))) N *
                toleranceDenominator ≤ N

/-- Fixed-width alphabet words and bounded block values describe the same
normality target. Every eventual quantifier and the base restriction remain.
-/
theorem normalInBase_iff_normalByWords (b : ℕ) :
    NormalInBase b ↔ NormalByWords b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro pattern hpat ha tolerance htol
    have hk : 1 ≤ pattern.length := List.length_pos_iff.mpr hpat
    obtain ⟨N0, hN0, hbound⟩ :=
      h.2 pattern.length hk (wordValue b pattern) (wordValue_lt ha) tolerance htol
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    rw [count_actualDigits_prefix h.1 hpat ha N]
    exact hbound N hN
  · intro h
    refine ⟨h.1, ?_⟩
    intro k hk j hj tolerance htol
    obtain ⟨pattern, ha, hlen, hvalue⟩ := exists_word_of_lt h.1 hj
    have hpat : pattern ≠ [] := List.length_pos_iff.mp (by omega)
    obtain ⟨N0, hN0, hbound⟩ := h.2 pattern hpat ha tolerance htol
    refine ⟨N0, hN0, ?_⟩
    intro N hN
    have hword := hbound N hN
    rw [count_actualDigits_prefix h.1 hpat ha N, hlen, hvalue] at hword
    exact hword

/-- For each fixed block length and tolerance, one positive threshold works
for every block value of that length. The threshold still depends on both
the length and tolerance; it is not uniform across all lengths.
-/
def UniformBlockNormality (b : ℕ) : Prop :=
  2 ≤ b ∧
    ∀ k : ℕ, 1 ≤ k →
      ∀ toleranceDenominator : ℕ, 1 ≤ toleranceDenominator →
        ∃ N0 : ℕ, 1 ≤ N0 ∧
          ∀ N : ℕ, N0 ≤ N →
            ∀ j : ℕ, j < b ^ k →
              Nat.dist ((b ^ k) * occurrences b k j N) N * toleranceDenominator ≤ N

/-- A finite collection of eventual predicates has a common positive threshold.
The induction chooses the maximum of the two thresholds at each new index.
-/
private theorem eventually_uniform_below (P : ℕ → ℕ → Prop) (limit : ℕ) :
    (∀ j : ℕ, j < limit → ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → P j N) →
      ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ j : ℕ, j < limit → P j N := by
  induction limit with
  | zero =>
    intro _
    refine ⟨1, by omega, ?_⟩
    intro N _ j hj
    omega
  | succ limit ih =>
    intro h
    obtain ⟨Nrest, hrest, prest⟩ := ih (by
      intro j hj
      exact h j (by omega))
    obtain ⟨Nlast, hlast, plast⟩ := h limit (by omega)
    refine ⟨max Nrest Nlast, le_trans hrest (Nat.le_max_left _ _), ?_⟩
    intro N hN j hj
    by_cases hjrest : j < limit
    · exact prest N (le_trans (Nat.le_max_left _ _) hN) j hjrest
    · have heq : j = limit := by omega
      subst j
      exact plast N (le_trans (Nat.le_max_right _ _) hN)

/-- Moving the bounded block-value quantifier after the threshold is valid
because a fixed width has finitely many values. Block length and tolerance
remain before the existential threshold in both statements.
-/
theorem normalInBase_iff_uniformBlockNormality (b : ℕ) :
    NormalInBase b ↔ UniformBlockNormality b := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro k hk tolerance htol
    apply eventually_uniform_below
    intro j hj
    exact h.2 k hk j hj tolerance htol
  · intro h
    refine ⟨h.1, ?_⟩
    intro k hk j hj tolerance htol
    obtain ⟨N0, hN0, hbound⟩ := h.2 k hk tolerance htol
    exact ⟨N0, hN0, fun N hN => hbound N hN j hj⟩

end GoldenNormality
