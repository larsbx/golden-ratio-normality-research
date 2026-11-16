import RidoutReplay
import Lean.Elab.Command
import Lean.Util.CollectAxioms

open scoped BigOperators

-- Fix the full imported statement independently of its displayed declaration.
example {ξ : ℝ} (halg : IsAlgebraic ℚ ξ) (S₁ S₂ : Finset Nat.Primes)
    {ε : ℝ} (hε : 0 < ε) :
    {β : ℚ | |ξ - (β : ℝ)| *
        (∏ l ∈ S₁, ((padicNorm (l : ℕ) β.num : ℚ) : ℝ)) *
        ∏ l ∈ S₂, ((padicNorm (l : ℕ) β.den : ℚ) : ℝ)
      ≤ (max β.num.natAbs β.den : ℝ) ^ (-2 - ε)}.Finite :=
  Rat.finite_setOf_ridout halg S₁ S₂ hε

-- These wrappers retain the actual source, all numerator/exponent quantifiers,
-- and the strict thresholds of the two zero-count consequences.
example : ∀ B : ℕ, 0 < B → ∃ M : ℕ, ∀ (m : ℕ) (p : ℤ), M ≤ m →
    1 ≤ |(2 : ℝ) ^ m * GoldenNormality.alpha - p| ^ B * (2 : ℝ) ^ m :=
  GoldenNormality.RidoutBridge.alpha_eventualDyadicSeparation

example (h : ℤ) (hh : h ≠ 0) (B : ℕ) (hB : 0 < B) :
    ∃ M : ℕ, ∀ (n : ℕ) (p : ℤ), M ≤ n →
      1 ≤ |(2 : ℝ) ^ n * ((h : ℝ) * GoldenNormality.alpha) - (p : ℝ)| ^ B * (2 : ℝ) ^ n :=
  GoldenNormality.RidoutBridge.fixedMultiplier_eventualDyadicSeparation h hh B hB

example (d : ℕ) (hd : 0 < d) (B : ℕ) (hB : 0 < B) :
    ∃ M : ℕ, ∀ (n : ℕ) (p : ℤ), M ≤ n →
      1 ≤ |GoldenNormality.BinaryDyadicOrbit.point (n + d) -
        GoldenNormality.BinaryDyadicOrbit.point n - (p : ℝ)| ^ B * (2 : ℝ) ^ n :=
  GoldenNormality.RidoutBridge.fixedLag_eventual_separation d hd B hB

example (d : ℕ) (hd : 0 < d) (B : ℕ) (hB : 0 < B) :
    ∃ M : ℕ, ∀ (n k : ℕ), M ≤ n →
      GoldenNormality.blockValue 2 (n + d) k = GoldenNormality.blockValue 2 n k → B * k < n :=
  GoldenNormality.RidoutBridge.fixedLag_repeatedBlock_mul_lt d hd B hB

-- The lag-two mode is three. Its signed counterpart also satisfies the estimate.
example : ∃ M : ℕ, ∀ (n : ℕ) (p : ℤ), M ≤ n →
    1 ≤ |(2 : ℝ) ^ n * (((-3 : ℤ) : ℝ) * GoldenNormality.alpha) - (p : ℝ)| ^ (2 : ℕ) *
      (2 : ℝ) ^ n :=
  GoldenNormality.RidoutBridge.fixedMultiplier_eventualDyadicSeparation (-3) (by decide) 2 (by decide)

-- At lag zero the orbit difference exactly equals the integer zero.
example (n : ℕ) : ¬ (1 ≤ |GoldenNormality.BinaryDyadicOrbit.point (n + 0) -
    GoldenNormality.BinaryDyadicOrbit.point n - ((0 : ℤ) : ℝ)| ^ (1 : ℕ) * (2 : ℝ) ^ n) := by
  simp

-- The actual overlapping repeat at starts 10 and 14 refutes a cutoff-free bound.
example : GoldenNormality.blockValue 2 (10 + 4) 6 = GoldenNormality.blockValue 2 10 6 ∧
    ¬ ((2 : ℕ) * 6 < 10) := by
  obtain ⟨h10, h14⟩ := GoldenNormality.BinaryDyadicOrbit.actual_overlapping_repeat
  exact ⟨h14.trans h10.symm, by decide⟩

example (c : ℝ) (hc : 0 ≤ c) (hcritical : c ^ 2 < 2) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.RidoutBridge.zero_count_eventually_exceeds c hc hcritical

example (c : ℝ) (hc : 0 ≤ c) (hcritical : Real.pi * c ^ 2 < 8) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.RidoutBridge.zero_count_exceeds c hc hcritical M

-- Exercise both conclusions at a positive coefficient, preserving their distinct quantifiers.
example : ∃ M : ℕ, ∀ N : ℕ, M ≤ N → Real.sqrt (N : ℝ) <
    (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  simpa using GoldenNormality.RidoutBridge.zero_count_eventually_exceeds 1
    (by norm_num) (by norm_num)

example (M : ℕ) : ∃ N : ℕ, M ≤ N ∧ Real.sqrt (N : ℝ) <
    (GoldenNormality.occurrences 2 1 0 N : ℝ) := by
  have hpi : Real.pi < 8 := lt_trans Real.pi_lt_four (by norm_num)
  simpa using GoldenNormality.RidoutBridge.zero_count_exceeds 1 (by norm_num)
    (by simpa using hpi) M

-- The algebraic rational 1/2 is in (0,1), but has exact dyadic approximants.
example (m : ℕ) : ¬ (1 ≤ |(2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) -
    ((2 : ℤ) ^ m : ℝ)| ^ (1 : ℕ) * (2 : ℝ) ^ (m + 1)) := by
  have he : (2 : ℝ) ^ (m + 1) * (1 / 2 : ℝ) - ((2 : ℤ) ^ m : ℝ) = 0 := by
    push_cast
    rw [pow_succ]
    ring
  rw [he]
  norm_num

-- Even the actual irrational alpha needs an eventual threshold.
example : ¬ (1 ≤ |(2 : ℝ) ^ 0 * GoldenNormality.alpha - (0 : ℤ)| ^ (1 : ℕ) *
    (2 : ℝ) ^ 0) := by
  simpa only [pow_zero, one_mul, Int.cast_zero, sub_zero, pow_one, mul_one,
    abs_of_pos GoldenNormality.alpha_pos] using
    (not_le.mpr GoldenNormality.alpha_lt_one)

#check GoldenNormality.RidoutBridge.alpha_eventualDyadicSeparation
#check GoldenNormality.RidoutBridge.fixedMultiplier_eventualDyadicSeparation
#check GoldenNormality.RidoutBridge.fixedLag_eventual_separation
#check GoldenNormality.RidoutBridge.fixedLag_repeatedBlock_mul_lt
#check GoldenNormality.RidoutBridge.zero_count_eventually_exceeds
#check GoldenNormality.RidoutBridge.zero_count_exceeds
#check Rat.finite_setOf_ridout
#check GoldenNormality.BinaryComplement.EventualDyadicSeparation
#check GoldenNormality.BinaryComplement.zero_count_eventually_exceeds_of_eventual_dyadic_separation
#check GoldenNormality.BinaryComplement.zero_count_exceeds_of_eventual_dyadic_separation

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  let targets := #[
    `GoldenNormality.RidoutBridge.finite_dyadicCandidates,
    `GoldenNormality.RidoutBridge.eventualDyadicSeparation_of_finite_candidates,
    `GoldenNormality.RidoutBridge.algebraic_alpha,
    `GoldenNormality.RidoutBridge.alpha_eventualDyadicSeparation,
    `GoldenNormality.RidoutBridge.fixedMultiplier_eventualDyadicSeparation,
    `GoldenNormality.RidoutBridge.fixedLag_eventual_separation,
    `GoldenNormality.RidoutBridge.fixedLag_repeatedBlock_mul_lt,
    `GoldenNormality.RidoutBridge.zero_count_eventually_exceeds,
    `GoldenNormality.RidoutBridge.zero_count_exceeds,
    `Rat.finite_setOf_ridout,
    `GoldenNormality.BinaryDyadicOrbit.irrational_alpha,
    `GoldenNormality.BinaryComplement.zero_count_eventually_exceeds_of_eventual_dyadic_separation,
    `GoldenNormality.BinaryComplement.zero_count_exceeds_of_eventual_dyadic_separation]
  for target in targets do
    let some info := env.find? target | throwError "Missing audited theorem {target}"
    if !info.isTheorem then throwError "Audited declaration is not a theorem: {target}"
    let axioms ← collectAxioms target
    for axiomName in axioms do
      if !allowed.contains axiomName then
        throwError "Unexpected transitive axiom for {target}: {axiomName}"
    liftIO <| IO.println s!"RIDOUT_AXIOMS\t{target}\t{axioms}"
  liftIO <| IO.println ("RIDOUT_CONTROLS\tone_eventually,one_arbitrarily_late,rational_half," ++
    "alpha_exponent_zero,negative_multiplier,lag_zero,overlapping_repeat_cutoff")
  liftIO <| IO.println "RIDOUT_AUDIT_COMPLETE"
