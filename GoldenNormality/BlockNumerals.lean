import GoldenNormality.Certificates

/-!
# Fixed-length block numerals

The value of a word is read most significant digit first.  Its length remains a
separate part of the encoding: leading zeroes are allowed, and injectivity below
requires equal lengths.  The resulting numeral is identified with `blockValue`
for every actual digit segment, retaining its zero-based starting position.
-/

namespace GoldenNormality

/-- The base-`b` value of a word, read most significant digit first. -/
def wordValue (b : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: rest => d * b ^ rest.length + wordValue b rest

/-- Every symbol belongs to the base-`b` digit alphabet. -/
def InAlphabet (b : ℕ) : List ℕ → Prop
  | [] => True
  | d :: rest => d < b ∧ InAlphabet b rest

instance (b : ℕ) (word : List ℕ) : Decidable (InAlphabet b word) := by
  induction word with
  | nil => exact isTrue trivial
  | cons d rest ih =>
    change Decidable (d < b ∧ InAlphabet b rest)
    letI : Decidable (InAlphabet b rest) := ih
    infer_instance

@[simp] theorem inAlphabet_nil (b : ℕ) : InAlphabet b [] := trivial

@[simp] theorem inAlphabet_cons_iff (b d : ℕ) (rest : List ℕ) :
    InAlphabet b (d :: rest) ↔ d < b ∧ InAlphabet b rest := Iff.rfl

/-- A valid word of length `k` represents a value strictly below `b^k`. -/
theorem wordValue_lt {b : ℕ} {word : List ℕ} (h : InAlphabet b word) :
    wordValue b word < b ^ word.length := by
  induction word with
  | nil => simp [wordValue]
  | cons d rest ih =>
    have hrest := ih h.2
    have hd : d + 1 ≤ b := Nat.succ_le_of_lt h.1
    have hmul := Nat.mul_le_mul_right (b ^ rest.length) hd
    simp only [wordValue, List.length_cons, pow_succ]
    nlinarith

/-- Equal-length words over the digit alphabet have distinct numeral values. -/
theorem wordValue_injective {b : ℕ} {left right : List ℕ}
    (hl : InAlphabet b left) (hr : InAlphabet b right)
    (hlen : left.length = right.length)
    (hv : wordValue b left = wordValue b right) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons e tail => simp at hlen
  | cons d rest ih =>
    cases right with
    | nil => simp at hlen
    | cons e tail =>
      have hlen' : rest.length = tail.length := by simpa using hlen
      have hrest := wordValue_lt hl.2
      have htail := wordValue_lt hr.2
      simp only [wordValue] at hv
      rw [← hlen'] at hv htail
      have hd : d = e := by
        apply Nat.le_antisymm
        · by_contra hde
          have hde' : e + 1 ≤ d := by omega
          have hmul := Nat.mul_le_mul_right (b ^ rest.length) hde'
          nlinarith
        · by_contra hed
          have hed' : d + 1 ≤ e := by omega
          have hmul := Nat.mul_le_mul_right (b ^ rest.length) hed'
          nlinarith
      subst e
      have hv' : wordValue b rest = wordValue b tail := by omega
      exact congrArg (List.cons d) (ih hl.2 hr.2 hlen' hv')

/-- Taking a prefix preserves the segment's original starting position. -/
theorem actualDigits_take (b start length k : ℕ) :
    (actualDigits b start length).take k =
      actualDigits b start (min k length) := by
  induction k generalizing start length with
  | zero => simp
  | succ k ih =>
    cases length with
    | zero => simp
    | succ length =>
      have hmin : min (k + 1) (length + 1) = min k length + 1 := by omega
      rw [hmin, actualDigits_succ b start length,
        actualDigits_succ b start (min k length), List.take_succ_cons, ih]

/-- Dropping digits shifts the segment's start and truncates its length. -/
theorem actualDigits_drop (b start length n : ℕ) :
    (actualDigits b start length).drop n =
      actualDigits b (start + n) (length - n) := by
  induction n generalizing start length with
  | zero => simp
  | succ n ih =>
    cases length with
    | zero => simp
    | succ length =>
      rw [actualDigits_succ, List.drop_succ_cons, ih]
      congr 1 <;> omega

/-- A window which fits in a segment is exactly the corresponding digit block. -/
theorem actualDigits_window (b start length n k : ℕ) (h : n + k ≤ length) :
    ((actualDigits b start length).drop n).take k =
      actualDigits b (start + n) k := by
  rw [actualDigits_drop, actualDigits_take,
    Nat.min_eq_left (show k ≤ length - n by omega)]

/-- Actual digits lie in the base alphabet. -/
theorem actualDigits_inAlphabet {b : ℕ} (hb : 0 < b) (start length : ℕ) :
    InAlphabet b (actualDigits b start length) := by
  induction length generalizing start with
  | zero => simp
  | succ length ih =>
    rw [actualDigits_succ]
    constructor
    · have hd := digit_range hb start
      omega
    · exact ih (start + 1)

/-- Positional evaluation of an actual digit segment equals its floor block. -/
theorem wordValue_actualDigits (b start length : ℕ) :
    (wordValue b (actualDigits b start length) : ℤ) =
      blockValue b start length := by
  induction length generalizing start with
  | zero => simp [wordValue, blockValue]
  | succ length ih =>
    rw [actualDigits_succ]
    simp only [wordValue, actualDigits_length, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    have hd : ((digit b start).toNat : ℤ) = digit b start := by
      have hnonneg : 0 ≤ digit b start := blockValue_nonneg b start 1
      omega
    rw [hd, ih]
    have hsplit := blockValue_append b start 1 length
    simpa [digit, Nat.add_comm, mul_comm] using hsplit.symm

/-- The natural-number form of the actual block numeral. -/
theorem wordValue_actualDigits_toNat (b start length : ℕ) :
    wordValue b (actualDigits b start length) = (blockValue b start length).toNat := by
  have h := congrArg Int.toNat (wordValue_actualDigits b start length)
  simpa only [Int.toNat_natCast] using h

/-- A valid pattern matches a block exactly when their fixed-length values agree. -/
theorem actualDigits_eq_iff_blockValue {b n : ℕ} (hb : 2 ≤ b)
    {pattern : List ℕ} (hp : InAlphabet b pattern) :
    actualDigits b n pattern.length = pattern ↔
      blockValue b n pattern.length = (wordValue b pattern : ℤ) := by
  constructor
  · intro h
    rw [← wordValue_actualDigits, h]
  · intro h
    have hbpos : 0 < b := by omega
    apply wordValue_injective (actualDigits_inAlphabet hbpos n pattern.length) hp
      (actualDigits_length b n pattern.length)
    have hv := (wordValue_actualDigits b n pattern.length).trans h
    exact_mod_cast hv

end GoldenNormality
