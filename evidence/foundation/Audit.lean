import GoldenNormality.Blocks
import GoldenNormality.Prefix
import GoldenNormality.Automaton
import GoldenNormality.Certificates
import GoldenNormality.Normality
import GoldenNormality
import GoldenNormality.Contracts
import Receipts
import Lean.Elab.Command
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array (Name × Nat) := #[(`GoldenNormality.Blocks, 1), (`GoldenNormality.Prefix, 1), (`GoldenNormality.Automaton, 1), (`GoldenNormality.Certificates, 1), (`GoldenNormality.Normality, 1), (`GoldenNormality, 0), (`GoldenNormality.Contracts, 1), (`Receipts, 1)]
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for (moduleName, minimumProofs) in targets do
    let some idx := env.getModuleIdx? moduleName | throwError "Missing audited module"
    let data := env.header.moduleData[idx.toNat]!
    for info in data.constants do
      if info.isAxiom then throwError "Local audited axiom"
    let mut count := 0
    let mut proofs := 0
    for info in data.constants do
      let name := info.name
      let axs ← collectAxioms name
      for ax in axs do
        if !allowed.contains ax then throwError "Nonstandard transitive axiom"
      count := count + 1
      if info.isTheorem then proofs := proofs + 1
      let names := String.intercalate "," (axs.toList.map toString)
      liftIO <| IO.println s!"GNR_AXIOMS	{moduleName}	{name}	{names}"
    if proofs < minimumProofs then throwError "Missing compiled proofs"
    liftIO <| IO.println s!"GNR_COMPLETE	{moduleName}	{count}	{proofs}"

#check GoldenNormality.Contracts.root
#check GoldenNormality.Contracts.adjacentPrefixes
#check GoldenNormality.Contracts.blockSemantics
#check GoldenNormality.Contracts.consecutiveCount
#check GoldenNormality.Contracts.chunkBoundary
#check GoldenNormality.Contracts.automatonLanguage
#check GoldenNormality.Contracts.automatonAllInputs
#check GoldenNormality.Contracts.automatonPowerInput
