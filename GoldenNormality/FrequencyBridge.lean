import GoldenNormality.BlockNumerals
import GoldenNormality.Normality

/-!
# Certified finite counts in the normality target

The executable list counter and the mathematical `occurrences` definition use
different presentations of the same event.  This module proves their equality
for every base, nonempty alphabet word, and finite digit prefix at the stated
hypotheses.  In particular, `L` digits give `L + 1 - k` complete starting
positions for a positive block length `k`; short prefixes give zero starts.

No asymptotic frequency estimate is assumed or established here.  The result
connects an existing finite certificate to the exact count occurring in
`NormalInBase`, including leading-zero patterns and overlapping occurrences.
-/

namespace GoldenNormality

private theorem countP_congr_on {α : Type} (text : List α) (p q : α → Bool) :
    (∀ x ∈ text, p x = q x) → text.countP p = text.countP q := by
  induction text with
  | nil => intro _; rfl
  | cons head rest ih =>
    intro h
    have hhead : p head = q head := h head (by simp)
    have hrest : rest.countP p = rest.countP q :=
      ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.countP_cons, hhead, hrest]

/-- Removing a tail of starts known to contribute zero does not change a count. -/
private theorem countP_range_cut (p : ℕ → Bool) (cut total : ℕ) (hcut : cut ≤ total)
    (hzero : ∀ i, cut ≤ i → i < total → p i = false) :
    (List.range total).countP p = (List.range cut).countP p := by
  induction total generalizing cut with
  | zero =>
    have hc : cut = 0 := by omega
    subst cut
    rfl
  | succ total ih =>
    by_cases hc : cut = total + 1
    · subst cut
      rfl
    · have hct : cut ≤ total := by omega
      have hlast : p total = false := hzero total hct (by omega)
      have htail : ∀ i, cut ≤ i → i < total → p i = false := by
        intro i hi ht
        exact hzero i hi (by omega)
      calc
        (List.range (total + 1)).countP p = (List.range total).countP p := by
          simp [List.range_succ, List.countP_append, hlast]
        _ = (List.range cut).countP p := ih cut hct htail

/-- The complete finite list count is exactly the count in the normality target.
The nonempty-pattern hypothesis is essential because `Blocks.count []` is zero.
-/
theorem count_actualDigits_eq_occurrences {b : ℕ} (hb : 2 ≤ b)
    {pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern) (L : ℕ) :
    Blocks.count pattern (actualDigits b 0 L) =
      occurrences b pattern.length (wordValue b pattern) (L + 1 - pattern.length) := by
  have hk : 1 ≤ pattern.length := List.length_pos_iff.mpr hpat
  rw [Blocks.count_eq_enumerated]
  simp only [Blocks.enumeratedCount, actualDigits_length]
  let p : ℕ → Bool := fun n => Blocks.occurs pattern ((actualDigits b 0 L).drop n)
  change (List.range L).countP p = _
  have hzero : ∀ n, L + 1 - pattern.length ≤ n → n < L → p n = false := by
    intro n hn hL
    dsimp only [p]
    apply Blocks.occurs_false_of_short
    simp only [List.length_drop, actualDigits_length]
    omega
  have hcut := countP_range_cut p (L + 1 - pattern.length) L (by omega) hzero
  rw [hcut]
  unfold occurrences
  apply countP_congr_on
  intro n hn
  have hn' : n < L + 1 - pattern.length := List.mem_range.mp hn
  have hfit : n + pattern.length ≤ L := by omega
  dsimp only [p, Blocks.occurs]
  apply decide_eq_decide.mpr
  rw [actualDigits_window b 0 L n pattern.length hfit, Nat.zero_add,
    actualDigits_eq_iff_blockValue (n := n) hb ha]
  exact ⟨And.right, fun h => ⟨hpat, h⟩⟩

/-- A prefix of length `N + k - 1` contains exactly the first `N` starts.
For `N = 0` this prefix has length `k - 1` and both counts are zero.  The main
theorem above also permits the empty prefix to certify zero starts.
-/
theorem count_actualDigits_prefix {b : ℕ} (hb : 2 ≤ b)
    {pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern) (N : ℕ) :
    Blocks.count pattern (actualDigits b 0 (N + pattern.length - 1)) =
      occurrences b pattern.length (wordValue b pattern) N := by
  have hk : 1 ≤ pattern.length := List.length_pos_iff.mpr hpat
  have he : N + pattern.length - 1 + 1 - pattern.length = N := by omega
  simpa only [he] using
    count_actualDigits_eq_occurrences hb hpat ha (N + pattern.length - 1)

/-- A proved native word binding transfers the counter to `occurrences`. -/
theorem certified_count_eq_occurrences {b : ℕ} (hb : 2 ≤ b)
    {text pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) :
    Blocks.count pattern text =
      occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length) := by
  calc
    Blocks.count pattern text = Blocks.count pattern (actualDigits b 0 text.length) :=
      congrArg (Blocks.count pattern) (digitsAt_eq_actualDigits digits)
    _ = _ := count_actualDigits_eq_occurrences hb hpat ha text.length

/-- A closed native count certificate now concerns the exact normality count. -/
theorem certified_occurrences_sound {b value : ℕ} (hb : 2 ≤ b)
    {text pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) (count : Blocks.count pattern text = value) :
    occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length) =
      value := by
  exact (certified_count_eq_occurrences hb hpat ha digits).symm.trans count

/-- Exact integer discrepancy is preserved by the source-bound count bridge. -/
theorem certified_discrepancy_eq {b value : ℕ} (hb : 2 ≤ b)
    {text pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) (count : Blocks.count pattern text = value) :
    Nat.dist ((b ^ pattern.length) *
      occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length))
        (text.length + 1 - pattern.length) =
      Nat.dist ((b ^ pattern.length) * value) (text.length + 1 - pattern.length) := by
  rw [certified_occurrences_sound hb hpat ha digits count]

/-- A finite discrepancy bound may be transferred, with its scale and tolerance
unchanged. This theorem does not add any eventual or uniform quantifier. -/
theorem certified_discrepancy_bound {b value tolerance bound : ℕ} (hb : 2 ≤ b)
    {text pattern : List ℕ} (hpat : pattern ≠ []) (ha : InAlphabet b pattern)
    (digits : DigitsAt b 0 text) (count : Blocks.count pattern text = value)
    (hbound : Nat.dist ((b ^ pattern.length) * value)
      (text.length + 1 - pattern.length) * tolerance ≤ bound) :
    Nat.dist ((b ^ pattern.length) *
      occurrences b pattern.length (wordValue b pattern) (text.length + 1 - pattern.length))
        (text.length + 1 - pattern.length) * tolerance ≤ bound := by
  rw [certified_discrepancy_eq hb hpat ha digits count]
  exact hbound

end GoldenNormality
