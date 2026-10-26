module
public import Lean

@[expose] public section

/-!
Inspect declarations in the substantive project and Solution namespaces using Lean's own transitive
axiom collector. This command emits theorem types and axiom lists without
printing large proof expressions. It creates no mathematical assumptions.
-/

open Lean Elab Command

elab "audit_math_and_theory" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let projectPrefixes : Array Name := #[`MathAndTheory, `QPermanentProblem,
    `DomiRankProblem, `BestOfNChallenge, `ConcavityChallenge, `HofstadterChallenge]
  let mut count : Nat := 0
  let mut declarationCount : Nat := 0
  for (name, info) in env.constants.toList do
    -- Module interfaces can export a proved theorem as an axiom-shaped
    -- declaration, while retaining its computed transitive axiom metadata.
    -- Inspect the proposition type, not only ConstantInfo.isTheorem.
    if projectPrefixes.any (fun namespacePrefix => namespacePrefix.isPrefixOf name) then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Unapproved axiom {axiomName} in declaration {name}"
      declarationCount := declarationCount + 1
      let isProposition ← liftTermElabM <| Meta.isProp info.type
      unless isProposition do
        continue
      let typeText ← liftTermElabM do
        return (← Meta.ppExpr info.type).pretty
      let report := Json.mkObj [
        ("name", toJson name.toString),
        ("type", toJson typeText),
        ("axioms", toJson (axioms.map Name.toString))]
      logInfo m!"LEAN_THEOREM_AUDIT {report.compress}"
      count := count + 1
  if count == 0 then
    throwError "No project theorem was loaded for the axiom audit"
  logInfo m!"LEAN_DECLARATION_AUDIT_PASS {declarationCount} declarations"
  logInfo m!"LEAN_AUDIT_PASS {count} theorems"
