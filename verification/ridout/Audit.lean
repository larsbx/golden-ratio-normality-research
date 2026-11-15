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

#check Rat.finite_setOf_ridout
#check GoldenNormality.BinaryComplement.EventualDyadicSeparation
#check GoldenNormality.BinaryComplement.zero_count_eventually_exceeds_of_eventual_dyadic_separation
#check GoldenNormality.BinaryComplement.zero_count_exceeds_of_eventual_dyadic_separation

open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[
    `Rat.finite_setOf_ridout,
    `GoldenNormality.BinaryDyadicOrbit.irrational_alpha,
    `GoldenNormality.BinaryComplement.zero_count_eventually_exceeds_of_eventual_dyadic_separation,
    `GoldenNormality.BinaryComplement.zero_count_exceeds_of_eventual_dyadic_separation]
  for target in targets do
    let axioms ← collectAxioms target
    for axiomName in axioms do
      if !allowed.contains axiomName then
        throwError "Unexpected transitive axiom for {target}: {axiomName}"
    liftIO <| IO.println s!"RIDOUT_AXIOMS\t{target}\t{axioms}"
  liftIO <| IO.println "RIDOUT_AUDIT_COMPLETE"
