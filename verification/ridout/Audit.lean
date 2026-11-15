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

example (c : ℝ) (hc : 0 ≤ c) (hcritical : c ^ 2 < 2) :
    ∃ M : ℕ, ∀ N : ℕ, M ≤ N → c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.RidoutBridge.zero_count_eventually_exceeds c hc hcritical

example (c : ℝ) (hc : 0 ≤ c) (hcritical : Real.pi * c ^ 2 < 8) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ c * Real.sqrt (N : ℝ) <
      (GoldenNormality.occurrences 2 1 0 N : ℝ) :=
  GoldenNormality.RidoutBridge.zero_count_exceeds c hc hcritical M

-- Algebraicity alone cannot imply the same all-numerator conclusion.
example (m : ℕ) : ¬ (1 ≤ |(2 : ℝ) ^ m * 0 - (0 : ℤ)| ^ (1 : ℕ) *
    (2 : ℝ) ^ m) := by simp

#check GoldenNormality.RidoutBridge.alpha_eventualDyadicSeparation
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
  liftIO <| IO.println "RIDOUT_AUDIT_COMPLETE"
