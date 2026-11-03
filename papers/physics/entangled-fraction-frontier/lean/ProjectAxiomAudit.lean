import AllProofs
import OptimizerComplementarity
import MarginalRank
import RectangularOptimizerRank
import NilpotentTensor
import NilpotentState
import Lean.Util.CollectAxioms

/-!
Complete transitive axiom audit of every declaration owned by the six
project modules. Selection uses the defining module, not a list of theorem
names, so private helpers and compiler-generated declarations are included.
The collector is the Lean utility used by `#print axioms`.

Names of the shapes stored by older Lean code generators (`_cstage1`,
`_cstage2`, `_spec_k`, `_elambda_k`, `_lambda_k`, `_closed_k`, `_boxed`,
`_rarg`) would be recorded as code-generation auxiliaries; the summary reports
how many occur. Every other declaration must be a non-axiom depending only on
`propext`, `Classical.choice` and `Quot.sound`.
-/

/-- Whether a name is a code-generation auxiliary of an older Lean compiler. -/
def MilneFef.Audit.isCodegenAuxiliary (name : Lean.Name) : Bool :=
  name.components.any fun component =>
    match component with
    | .str _ s => s.startsWith "_cstage" || s.startsWith "_spec_" ||
        s.startsWith "_elambda_" || s.startsWith "_lambda_" ||
        s.startsWith "_closed_" || s == "_boxed" || s == "_rarg"
    | _ => false

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open Lean Elab Command in
run_cmd do
  let modules : Array Name := #[`AllProofs, `OptimizerComplementarity, `MarginalRank, `RectangularOptimizerRank, `NilpotentTensor, `NilpotentState]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let env ← getEnv
  for moduleName in modules do
    unless (env.getModuleIdx? moduleName).isSome do
      throwError m!"Production module missing from environment: {moduleName}"
  let declarations ← env.constants.foldM
    (init := (#[] : Array (Name × Name × String))) fun acc name info => do
      match env.getModuleIdxFor? name with
      | none => pure acc
      | some index =>
        let owner := env.header.moduleNames[index.toNat]!
        if modules.contains owner then
          let kind := match info with
            | .axiomInfo _ => "axiom"
            | .defnInfo _ => "definition"
            | .thmInfo _ => "theorem"
            | .opaqueInfo _ => "opaque"
            | .quotInfo _ => "quotient"
            | .inductInfo _ => "inductive"
            | .ctorInfo _ => "constructor"
            | .recInfo _ => "recursor"
          pure (acc.push (owner, name, kind))
        else pure acc
  let declarations := declarations.qsort (fun a b => Name.lt a.2.1 b.2.1)
  let mut rejected : Array Name := #[]
  let mut auxiliaries : Nat := 0
  for (owner, name, kind) in declarations do
    let axioms ← collectAxioms name
    let axioms := axioms.qsort Name.lt
    let auxiliary := MilneFef.Audit.isCodegenAuxiliary name
    if auxiliary then
      auxiliaries := auxiliaries + 1
      if axioms.any (fun ax => !(allowed.contains ax || ax == `lcProof ||
          MilneFef.Audit.isCodegenAuxiliary ax)) then
        rejected := rejected.push name
    else if kind == "axiom" || axioms.any (fun ax => !allowed.contains ax) then
      rejected := rejected.push name
    let record := Json.mkObj [
      ("module", toJson owner.toString),
      ("name", toJson name.toString),
      ("kind", toJson kind),
      ("codegen_auxiliary", toJson auxiliary),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"FEF_AXIOM_DECL {record.compress}"
  let mut counts : List (String × Json) := []
  for moduleName in modules do
    let count := (declarations.filter (fun entry => entry.1 == moduleName)).size
    if count == 0 then
      throwError m!"Production module had zero audited declarations: {moduleName}"
    counts := counts ++ [(moduleName.toString, toJson count)]
  let summary := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("collector", toJson "Lean.collectAxioms"),
    ("selection", toJson "Environment.getModuleIdxFor? defining module; no name blacklist; code-generation auxiliaries classified by name"),
    ("modules", toJson (modules.map Name.toString)),
    ("counts", Json.mkObj counts),
    ("total", toJson declarations.size),
    ("codegen_auxiliaries", toJson auxiliaries),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("rejected", toJson (rejected.map Name.toString))]
  logInfo m!"FEF_AXIOM_SUMMARY {summary.compress}"
  unless rejected.isEmpty do
    throwError m!"Nonstandard transitive axioms in declarations: {rejected.toList}"


#print axioms MilneNew.Qubit.fef_frontier_standard
#print axioms MilneNew.Qubit.frontier_sharp
#print axioms MilneNew.Qubit.quantum_stability_coefficient_optimal_closed
#print axioms MilneExpanded.quantum_overlap_bound
#print axioms MilneContinuation.psd_rank_le_marginal_rank_product
#print axioms MilneContinuation.every_optimizer_explicit_rectangular_rank_bound
#print axioms MilneContinuation.every_full_schmidt_optimizer_rank_bound
#print axioms MilneContinuation.NilpotentState.counterexampleState_is_density
#print axioms MilneContinuation.NilpotentTensor.tensor_determinant
