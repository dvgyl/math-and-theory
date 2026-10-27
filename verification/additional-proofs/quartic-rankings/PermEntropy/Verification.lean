import PermEntropy.TheoremAll
import PermEntropy.RankingEquiv
import PermEntropy.PermutationTheorem
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! # Reproducible theorem and axiom audit

The commands in this file inspect declarations already checked by Lean.
They do not construct or change proofs. Both public project theorems and
private project helper theorems are checked transitively. The only allowed
axioms are the usual Lean foundation constants listed explicitly below.

Source-level axiom declarations are separately rejected by the source checker.
Lean's compiler also registers execution-only auxiliary declarations, such as
`_elambda` closures, in the elaboration environment. These are not themselves
mathematical theorems. No auxiliary name is exempted from the transitive
axiom whitelist if it occurs in any audited theorem's proof or type.
-/

#check PermEntropy.FinDist.entropy_of_pairwise_bias_all
#check PermEntropy.FinDist.entropy_quartic_log_factorial_all
#check PermEntropy.FinDist.entropy_of_pairwise_bias_equiv_all
#check PermEntropy.Ranking.card_eq_factorial
#check PermEntropy.exists_normalized_cut

#print axioms PermEntropy.FinDist.entropy_of_pairwise_bias_all
#print axioms PermEntropy.FinDist.entropy_quartic_log_factorial_all
#print axioms PermEntropy.FinDist.entropy_of_pairwise_bias_equiv_all
#print axioms PermEntropy.Ranking.card_eq_factorial
#print axioms PermEntropy.exists_normalized_cut

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let kernelEnv := env.checked.get
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let endpoints : Array Name := #[
    ``PermEntropy.FinDist.entropy_of_pairwise_bias_all,
    ``PermEntropy.FinDist.entropy_quartic_log_factorial_all,
    ``PermEntropy.FinDist.entropy_of_pairwise_bias_equiv_all,
    ``PermEntropy.Ranking.card_eq_factorial,
    ``PermEntropy.exists_normalized_cut]
  for name in endpoints do
    let some info := kernelEnv.find? name
      | throwError "Required endpoint is absent from the kernel environment: {name}"
    unless info.isTheorem do
      throwError "Required endpoint is not a theorem declaration: {name}"
    logInfo m!"Endpoint checked as theorem: {name}"
  let mut theoremCount : Nat := 0
  let mut privateCount : Nat := 0
  let mut observed : Array Name := #[]
  for (name, info) in env.constants do
    let isProject := (`PermEntropy).isPrefixOf name ||
      (`_private.PermEntropy).isPrefixOf name ||
      (`PermEntropy).isPrefixOf (privateToUserName name)
    if isProject then
      match kernelEnv.find? name with
      | none =>
        if info.isTheorem then
          throwError "Project theorem is absent from the kernel environment: {name}"
      | some checked =>
        if info.isTheorem && !checked.isTheorem then
          throwError "Project theorem has a different kernel declaration kind: {name}"
        if checked.isTheorem then
          let dependencies ← collectAxioms name
          for axiomName in dependencies do
            unless allowed.contains axiomName do
              throwError "Forbidden transitive axiom {axiomName} in theorem {name}"
            unless observed.contains axiomName do
              observed := observed.push axiomName
          theoremCount := theoremCount + 1
          if isPrivateName name then
            privateCount := privateCount + 1
  if theoremCount = 0 then
    throwError "The project theorem audit found no declarations."
  logInfo m!"Verified transitive axiom whitelist for {theoremCount} project theorem declarations, including {privateCount} private helper declarations."
  logInfo m!"Allowed foundation axioms: {allowed}"
  logInfo m!"Observed foundation axioms: {observed}"
