import BergeC5.Main
import Lean.Util.CollectAxioms

/-!
Complete transitive axiom audit of all declarations owned by local production
modules. Selection uses the defining module, not a list of public theorem names.
Private helpers and compiler-generated declarations are therefore included.
The collector is the same Lean utility used by `#print axioms`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open Lean Elab Command in
run_cmd do
  let modules : Array Name := #[`BergeC5.Basic, `BergeC5.Glue, `BergeC5.Check,
    `BergeC5.Main]
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
    logInfo m!"OPT_B_AXIOM_DECL {record.compress}"
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
  logInfo m!"OPT_B_AXIOM_SUMMARY {summary.compress}"
  unless rejected.isEmpty do
    throwError m!"Nonstandard transitive axioms in declarations: {rejected.toList}"

#check @BergeC5.exists_saturated_interval
#check @BergeC5.exists_saturated_lower
#check @BergeC5.satNumber_le_lower
#check @BergeC5.exists_saturated_cone
#check @BergeC5.satNumber_small
#check @BergeC5.Realizable.add
#print axioms BergeC5.exists_saturated_interval
#print axioms BergeC5.exists_saturated_lower
#print axioms BergeC5.satNumber_le_lower
#print axioms BergeC5.exists_saturated_cone
#print axioms BergeC5.satNumber_small
#print axioms BergeC5.Realizable.add
