import GoldenNormality.Automaton
import Mathlib.Data.Nat.Fib.Zeckendorf

/-!
# Total Fibonacci-word encoding

Mathlib's Zeckendorf representation lists descending Fibonacci indices, with
successive indices separated by at least two.  This module converts that list
to the most-significant-first Boolean words consumed by the binary automaton.
The rightmost bit retains weight `F_2 = 1`; zero is represented by the empty word.
-/

namespace GoldenNormality.BinaryAutomaton

private def indicesWord : List ℕ → List Bool
  | [] => []
  | a :: indices =>
    let rest := indicesWord indices
    true :: (List.replicate (a - 2 - rest.length) false ++ rest)

private theorem rep_tail {a : ℕ} {indices : List ℕ}
    (h : (a :: indices).IsZeckendorfRep) : indices.IsZeckendorfRep := by
  unfold List.IsZeckendorfRep at h ⊢
  simpa only [List.cons_append, List.tail_cons] using h.tail

private theorem rep_gap {a b : ℕ} {indices : List ℕ}
    (h : (a :: b :: indices).IsZeckendorfRep) : b + 2 ≤ a := by
  have hc : (a :: b :: (indices ++ [0])).IsChain (fun x y : ℕ => y + 2 ≤ x) := h
  exact (List.isChain_cons_cons.mp hc).1

private theorem rep_head_ge_two {a : ℕ} {indices : List ℕ}
    (h : (a :: indices).IsZeckendorfRep) : 2 ≤ a := by
  cases indices with
  | nil => simpa [List.IsZeckendorfRep, List.isChain_cons_cons] using h
  | cons b indices =>
    have hgap := rep_gap h
    omega

private theorem indicesWord_length {indices : List ℕ} (h : indices.IsZeckendorfRep) :
    (indicesWord indices).length = indices.headD 1 - 1 := by
  induction indices with
  | nil => rfl
  | cons a indices ih =>
    have ht := rep_tail h
    have hlen := ih ht
    have ha := rep_head_ge_two h
    have hbound : (indicesWord indices).length ≤ a - 2 := by
      cases indices with
      | nil => simp [indicesWord]
      | cons b indices =>
        have hgap := rep_gap h
        simp only [List.headD_cons] at hlen
        omega
    simp only [indicesWord, List.length_cons, List.length_append,
      List.length_replicate, List.headD_cons]
    omega

private theorem indicesWord_tail_bound {a : ℕ} {indices : List ℕ}
    (h : (a :: indices).IsZeckendorfRep) : (indicesWord indices).length ≤ a - 2 := by
  have hlen := indicesWord_length (rep_tail h)
  cases indices with
  | nil => simp [indicesWord]
  | cons b indices =>
    have hgap := rep_gap h
    simp only [List.headD_cons] at hlen
    omega

private theorem admissible_false_padding {word : List Bool} (h : Admissible word) (n : ℕ) :
    Admissible (List.replicate n false ++ word) := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [List.replicate_succ, Admissible, AdmissibleFrom] using ih

private theorem admissibleFrom_false_padding {word : List Bool} (h : Admissible word)
    (n : ℕ) (hn : 0 < n) (previous : Bool) :
    AdmissibleFrom previous (List.replicate n false ++ word) := by
  cases n with
  | zero => omega
  | succ n =>
    rw [List.replicate_succ, List.cons_append]
    exact ⟨by intro _; rfl, admissible_false_padding h n⟩

private theorem admissibleFrom_false_replicate (previous : Bool) (n : ℕ) :
    AdmissibleFrom previous (List.replicate n false) := by
  induction n generalizing previous with
  | zero => trivial
  | succ n ih =>
    rw [List.replicate_succ]
    exact ⟨by intro _; rfl, ih false⟩

private theorem indicesWord_admissible {indices : List ℕ} (h : indices.IsZeckendorfRep) :
    Admissible (indicesWord indices) := by
  induction indices with
  | nil => trivial
  | cons a indices ih =>
    have ht := rep_tail h
    have hadm := ih ht
    have hlen := indicesWord_length ht
    have hpad : AdmissibleFrom true
        (List.replicate (a - 2 - (indicesWord indices).length) false ++ indicesWord indices) := by
      cases indices with
      | nil =>
        simpa [indicesWord] using admissibleFrom_false_replicate true (a - 2)
      | cons b indices =>
        have hgap := rep_gap h
        have hb := rep_head_ge_two ht
        simp only [List.headD_cons] at hlen
        exact admissibleFrom_false_padding hadm _ (by omega) true
    exact ⟨by simp, hpad⟩

private theorem fibonacciSum_false_padding (n : ℕ) (word : List Bool) (k : ℕ) :
    fibonacciSum (List.replicate n false ++ word) k = fibonacciSum word k := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, fibonacciSum, bitValue, ih]

private theorem fibonacciSum_indicesWord {indices : List ℕ} (h : indices.IsZeckendorfRep) :
    fibonacciSum (indicesWord indices) 2 = (indices.map Nat.fib).sum := by
  induction indices with
  | nil => rfl
  | cons a indices ih =>
    have ht := rep_tail h
    have ha := rep_head_ge_two h
    have hbound := indicesWord_tail_bound h
    have hindex : a - 2 - (indicesWord indices).length + (indicesWord indices).length + 2 = a :=
      by omega
    simp [indicesWord, fibonacciSum, bitValue, hindex, fibonacciSum_false_padding, ih ht]

/-- A computable admissible Fibonacci word representing every natural number. -/
def encode (q : ℕ) : List Bool := indicesWord (Nat.zeckendorf q)

@[simp] theorem encode_zero : encode 0 = [] := by simp [encode, indicesWord]

/-- The total encoder always produces a word accepted by the automaton's input language. -/
theorem encode_admissible (q : ℕ) : Admissible (encode q) :=
  indicesWord_admissible (Nat.isZeckendorfRep_zeckendorf q)

/-- The encoded word has exactly the requested value with least weight `F_2`. -/
theorem fibonacciSum_encode (q : ℕ) : fibonacciSum (encode q) 2 = q := by
  rw [encode, fibonacciSum_indicesWord (Nat.isZeckendorfRep_zeckendorf q)]
  exact Nat.sum_zeckendorf_fib q

end GoldenNormality.BinaryAutomaton
