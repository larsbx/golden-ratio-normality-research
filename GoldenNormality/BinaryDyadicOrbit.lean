import GoldenNormality.Normality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Exact orbit and Fourier identities for the binary normality target. -/

namespace GoldenNormality.BinaryDyadicOrbit

open scoped BigOperators Topology
open Filter

/-- The orbit on the unit interval, at the same start as the block count. -/
noncomputable def point (n : ℕ) : ℝ := Int.fract ((2 : ℝ) ^ n * alpha)

/-- Half-open cells are essential to the floor-count correspondence. -/
theorem blockValue_eq_iff (n k j : ℕ) :
    blockValue 2 n k = (j : ℤ) ↔
      (j : ℝ) / (2 : ℝ) ^ k ≤ point n ∧
        point n < ((j : ℝ) + 1) / (2 : ℝ) ^ k := by
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [blockValue_eq_floor_fract]
  change Int.floor ((2 : ℝ) ^ k * point n) = (j : ℤ) ↔ _
  rw [Int.floor_eq_iff, div_le_iff₀ hp, lt_div_iff₀ hp]
  simp only [Int.cast_natCast, mul_comm ((2 : ℝ) ^ k)]

/-- Counts in a half-open dyadic cell, with multiplicity in orbit order. -/
noncomputable def cellCount (k j N : ℕ) : ℕ :=
  (List.range N).countP (fun n => decide
    ((j : ℝ) / (2 : ℝ) ^ k ≤ point n ∧
      point n < ((j : ℝ) + 1) / (2 : ℝ) ^ k))

theorem cellCount_eq_occurrences (k j N : ℕ) :
    cellCount k j N = occurrences 2 k j N := by
  unfold cellCount occurrences
  congr 1
  funext n
  by_cases h : blockValue 2 n k = (j : ℤ)
  · simp [h, (blockValue_eq_iff n k j).mp h]
  · have hc := mt (blockValue_eq_iff n k j).mpr h
    simp [h, hc]

/-- The same all-width condition on cell visits is precisely binary normality. -/
theorem normalInBase_iff_dyadic_cells :
    NormalInBase 2 ↔
      ∀ k : ℕ, 1 ≤ k → ∀ j : ℕ, j < 2 ^ k →
        ∀ T : ℕ, 1 ≤ T → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
          Nat.dist (2 ^ k * cellCount k j N) N * T ≤ N := by
  simp [NormalInBase, cellCount_eq_occurrences]

/-- Fourier character evaluated before reducing the orbit modulo one. -/
noncomputable def character (h : ℤ) (n : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * (h : ℝ) * ((2 : ℝ) ^ n * alpha)) : ℝ) : ℂ) *
    Complex.I)

theorem norm_character (h : ℤ) (n : ℕ) : ‖character h n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem character_eq_of_fract (h : ℤ) (n : ℕ) :
    character h n = Complex.exp
      ((((2 * Real.pi * (h : ℝ) * point n) : ℝ) : ℂ) * Complex.I) := by
  let x := (2 : ℝ) ^ n * alpha
  let q := Int.floor x
  have hx : x = point n + (q : ℝ) := (Int.fract_add_floor x).symm
  have he : 2 * Real.pi * (h : ℝ) * x =
      2 * Real.pi * (h : ℝ) * point n + 2 * Real.pi * (h : ℝ) * (q : ℝ) := by
    rw [hx]
    ring
  unfold character
  change Complex.exp (((2 * Real.pi * (h : ℝ) * x : ℝ) : ℂ) * Complex.I) = _
  rw [he, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hp : (((2 * Real.pi * (h : ℝ) * (q : ℝ) : ℝ) : ℂ) * Complex.I) =
      ((h * q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hp, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem character_shift (h : ℤ) (n d : ℕ) :
    character h (n + d) = character ((2 : ℤ) ^ d * h) n := by
  unfold character
  congr 1
  push_cast
  rw [pow_add]
  ring

/-- A positive lag in the usual Fourier autocorrelation produces another
mode on the same orbit, with multiplier `2^d - 1`. -/
theorem character_lag_difference (h : ℤ) (n d : ℕ) :
    character h (n + d) * character (-h) n =
      character (((2 : ℤ) ^ d - 1) * h) n := by
  rw [character_shift]
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Fourier averages retain the exact base-two orbit, and use all `N` starts. -/
noncomputable def average (h : ℤ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N, character h n) / (N : ℂ)

theorem norm_average_double_sub (h : ℤ) (N : ℕ) :
    ‖average (2 * h) N - average h N‖ ≤ 2 / (N : ℝ) := by
  have hshift (n : ℕ) : character (2 * h) n = character h (n + 1) := by
    simpa using (character_shift h n 1).symm
  have hsum : (∑ n ∈ Finset.range N, character (2 * h) n) + character h 0 =
      (∑ n ∈ Finset.range N, character h n) + character h N := by
    simp_rw [hshift]
    exact (Finset.sum_range_succ' (character h) N).symm.trans
      (Finset.sum_range_succ (character h) N)
  have he : average (2 * h) N - average h N =
      (character h N - character h 0) / (N : ℂ) := by
    unfold average
    rw [← sub_div]
    congr 1
    linear_combination hsum
  rw [he, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [norm_character, one_add_one_eq_two] using
    (norm_sub_le (character h N) (character h 0))

theorem tendsto_average_double_sub (h : ℤ) :
    Tendsto (fun N => average (2 * h) N - average h N) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  · intro N
    exact norm_nonneg _
  · exact norm_average_double_sub h

theorem tendsto_average_double_iff (h : ℤ) :
    Tendsto (average (2 * h)) atTop (𝓝 0) ↔ Tendsto (average h) atTop (𝓝 0) := by
  have hd := tendsto_average_double_sub h
  constructor
  · intro hh
    have he : (fun N => average (2 * h) N - (average (2 * h) N - average h N)) = average h := by
      funext N
      ring
    have ht := hh.sub hd
    rwa [he, sub_zero] at ht
  · intro hh
    have he : (fun N => average (2 * h) N - average h N + average h N) = average (2 * h) := by
      funext N
      ring
    have ht := hd.add hh
    rwa [he, add_zero] at ht

/-- Only the odd Fourier modes require an independent cancellation estimate. -/
theorem all_nonzero_modes_iff_odd_modes :
    (∀ h : ℤ, h ≠ 0 → Tendsto (average h) atTop (𝓝 0)) ↔
      (∀ h : ℤ, h % 2 = 1 → Tendsto (average h) atTop (𝓝 0)) := by
  constructor
  · intro hh h ho
    exact hh h (by omega)
  · intro hh
    have aux (m : ℕ) : ∀ h : ℤ, h.natAbs = m → h ≠ 0 →
        Tendsto (average h) atTop (𝓝 0) := by
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro h habs hne
        by_cases ho : h % 2 = 1
        · exact hh h ho
        · let q := h / 2
          have he : h = 2 * q := by dsimp [q]; omega
          have hq : q ≠ 0 := by intro hz; simp [he, hz] at hne
          have hmul : h.natAbs = 2 * q.natAbs := by
            rw [he, Int.natAbs_mul]
            rfl
          have hpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq
          have ht := ih q.natAbs (by omega) q rfl hq
          rw [he]
          exact (tendsto_average_double_iff q).mpr ht
    intro h hne
    exact aux h.natAbs h rfl hne

/-- The position-wise alternation is a control for count-only arguments. -/
def alternating (n : ℕ) : ℕ := (n + 1) % 2

def alternatingZeroCount (N : ℕ) : ℕ :=
  (List.range N).countP (fun n => decide (alternating n = 0))

private theorem alternatingZeroCount_eq (N : ℕ) : alternatingZeroCount N = N / 2 := by
  induction N with
  | zero => rfl
  | succ N ih =>
    unfold alternatingZeroCount
    rw [List.range_succ, List.countP_append]
    unfold alternatingZeroCount at ih
    rw [ih]
    by_cases h : alternating N = 0
    · have he : ([N] : List ℕ).countP (fun n => decide (alternating n = 0)) = 1 := by simp [h]
      rw [he]
      change N / 2 + 1 = (N + 1) / 2
      unfold alternating at h
      omega
    · have he : ([N] : List ℕ).countP (fun n => decide (alternating n = 0)) = 0 := by simp [h]
      rw [he, Nat.add_zero]
      change N / 2 = (N + 1) / 2
      unfold alternating at h
      omega

/-- The count-only parity bound and eventual domination of every square-root
threshold hold for an alternating sequence, which misses the word `00` at
every start. The control concerns these scalar consequences, with no carry
recurrence assumption on the alternating sequence. -/
theorem alternating_count_control :
    (∀ N : ℕ, 2 ≤ N → N ≤ alternatingZeroCount N ^ 2 + 7 * alternatingZeroCount N) ∧
    (∀ C : ℝ, 0 ≤ C → ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      C * Real.sqrt (N : ℝ) < (alternatingZeroCount N : ℝ)) ∧
    (∀ n : ℕ, ¬ (alternating n = 0 ∧ alternating (n + 1) = 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N hN
    rw [alternatingZeroCount_eq]
    have hhalf : 1 ≤ N / 2 := by omega
    nlinarith (config := { splitNe := false }) only [hhalf,
      show N ≤ 2 * (N / 2) + 1 by omega]
  · intro C hC
    obtain ⟨m, hm⟩ := exists_nat_gt (3 * C + 1)
    refine ⟨max 3 (m ^ 2), ?_⟩
    intro N hN
    have h3 : 3 ≤ N := (le_max_left _ _).trans hN
    have hmsq : m ^ 2 ≤ N := (le_max_right _ _).trans hN
    have hr : (m : ℝ) ≤ Real.sqrt (N : ℝ) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast hmsq)
    have ht : 0 < Real.sqrt (N : ℝ) :=
      Real.sqrt_pos_of_pos (by exact_mod_cast (show 0 < N by omega))
    have hstrict : 3 * C < Real.sqrt (N : ℝ) := by linarith only [hm, hr]
    have hmul := mul_lt_mul_of_pos_right hstrict ht
    rw [alternatingZeroCount_eq]
    have hhalf : (N : ℝ) ≤ 3 * (↑(N / 2) : ℝ) := by
      exact_mod_cast (show N ≤ 3 * (N / 2) by omega)
    nlinarith only [hmul, hhalf, Real.sq_sqrt (Nat.cast_nonneg N)]
  · intro n
    unfold alternating
    omega

end GoldenNormality.BinaryDyadicOrbit
