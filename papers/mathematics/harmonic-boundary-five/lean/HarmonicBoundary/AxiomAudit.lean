import HarmonicBoundary
import Lean

/-!
Complete transitive axiom audit of all declarations owned by the project modules.
Selection uses the defining module, not a list of public theorem names, so private
helpers and compiler-generated declarations are included. `WedgeAudit` and
`LocalFeasibility` only import other modules and print axioms; they define nothing.
The collector is the same Lean utility used by `#print axioms`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open Lean Elab Command in
run_cmd do
  let modules : Array Name := #[
    `HarmonicBoundary.DistanceCertificate, `HarmonicBoundary.BlockBudget, `HarmonicBoundary.WedgeDistance,
    `HarmonicBoundary.WedgeBoundary, `HarmonicBoundary.RootSectors, `HarmonicBoundary.Sharp14,
    `HarmonicBoundary.BipartiteSubcubic, `HarmonicBoundary.RootedMetricTruncation, `HarmonicBoundary.EvenEqualityAutomaton,
    `HarmonicBoundary.OddEqualityGrammar, `HarmonicBoundary.OddCountingIdentities, `HarmonicBoundary.LocalSystems.LocalSystems0000,
    `HarmonicBoundary.LocalSystems.LocalSystems0020, `HarmonicBoundary.LocalSystems.LocalSystems0040, `HarmonicBoundary.LocalSystems.LocalSystems0060,
    `HarmonicBoundary.LocalSystems.LocalSystems0080, `HarmonicBoundary.LocalSystems.LocalSystems0100, `HarmonicBoundary.LocalSystems.LocalSystems0120,
    `HarmonicBoundary.LocalSystems.LocalSystems0140, `HarmonicBoundary.LocalSystems.LocalSystems0160, `HarmonicBoundary.LocalSystems.LocalSystems0180,
    `HarmonicBoundary.LocalSystems.LocalSystems0200, `HarmonicBoundary.LocalSystems.LocalSystems0220, `HarmonicBoundary.LocalSystems.LocalSystems0240,
    `HarmonicBoundary.LocalSystems.LocalSystems0260, `HarmonicBoundary.LocalSystems.LocalSystems0280, `HarmonicBoundary.LocalSystems.LocalSystems0300,
    `HarmonicBoundary.LocalSystems.LocalSystems0320, `HarmonicBoundary.LocalSystems.LocalSystems0340, `HarmonicBoundary.LocalSystems.LocalSystems0360,
    `HarmonicBoundary.LocalSystems.LocalSystems0380, `HarmonicBoundary.LocalSystems.LocalSystems0400, `HarmonicBoundary.LocalSystems.LocalSystems0420,
    `HarmonicBoundary.LocalSystems.LocalSystems0440, `HarmonicBoundary.LocalSystems.LocalSystems0460, `HarmonicBoundary.LocalSystems.LocalSystems0480,
    `HarmonicBoundary.LocalSystems.LocalSystems0500, `HarmonicBoundary.LocalSystems.LocalSystems0520, `HarmonicBoundary.LocalSystems.LocalSystems0540,
    `HarmonicBoundary.LocalSystems.LocalSystems0560, `HarmonicBoundary.LocalSystems.LocalSystems0580, `HarmonicBoundary.LocalSystems.LocalSystems0600,
    `HarmonicBoundary.LocalSystems.LocalSystems0620, `HarmonicBoundary.LocalSystems.LocalSystems0640, `HarmonicBoundary.LocalSystems.LocalSystems0660,
    `HarmonicBoundary.LocalSystems.LocalSystems0680, `HarmonicBoundary.LocalSystems.LocalSystems0700, `HarmonicBoundary.LocalSystems.LocalSystems0720,
    `HarmonicBoundary.LocalSystems.LocalSystems0740, `HarmonicBoundary.LocalSystems.LocalSystems0760, `HarmonicBoundary.LocalSystems.LocalSystems0780,
    `HarmonicBoundary.LocalSystems.LocalSystems0800, `HarmonicBoundary.LocalSystems.LocalSystems0820]
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
  for (owner, name, kind) in declarations do
    let axioms ← collectAxioms name
    let axioms := axioms.qsort Name.lt
    if axioms.any (fun ax => !allowed.contains ax) then
      rejected := rejected.push name
    let record := Json.mkObj [
      ("module", toJson owner.toString),
      ("name", toJson name.toString),
      ("kind", toJson kind),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"HB_AXIOM_DECL {record.compress}"
  let mut counts : List (String × Json) := []
  for moduleName in modules do
    let count := (declarations.filter (fun entry => entry.1 == moduleName)).size
    if count == 0 then
      throwError m!"Production module had zero audited declarations: {moduleName}"
    counts := counts ++ [(moduleName.toString, toJson count)]
  let summary := Json.mkObj [
    ("schema", toJson (1 : Nat)),
    ("collector", toJson "Lean.collectAxioms"),
    ("selection", toJson "Environment.getModuleIdxFor? defining module; no name blacklist"),
    ("modules", toJson (modules.map Name.toString)),
    ("counts", Json.mkObj counts),
    ("total", toJson declarations.size),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("rejected", toJson (rejected.map Name.toString))]
  logInfo m!"HB_AXIOM_SUMMARY {summary.compress}"
  unless rejected.isEmpty do
    throwError m!"Nonstandard transitive axioms in declarations: {rejected.toList}"

#check @HarmonicBoundary.RootSectors.degree_three_noncut_nonboundary_six
#check @HarmonicBoundary.Sharp14.boundary_exactly_the_five_leaves
#check @HarmonicBoundary.BipartiteSubcubic.boundary_iff_leaf_or_cycle
#check @HarmonicBoundary.RootedMetricTruncation.diameter_bound
#check @HarmonicBoundary.exact_block_budget
