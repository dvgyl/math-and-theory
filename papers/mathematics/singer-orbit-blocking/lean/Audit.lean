import SingerC3
import Lean.Util.CollectAxioms

/-!
Axiom audit. Run with `lake env lean Audit.lean`.

The command below collects the transitive axioms of every declaration defined in the project
modules, selected by defining module rather than by name, so private helpers, generated
declarations and all 342 certificate searches are included. It fails unless each depends only
on `propext`, `Classical.choice` and `Quot.sound`. The `#print axioms` lines report the
principal declarations listed in `theorem-map.json`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let isProject (m : Name) : Bool := m == `SingerC3 || (`SingerC3).isPrefixOf m
  let modules := env.header.moduleNames.filter isProject
  let declarations ← env.constants.foldM (init := (#[] : Array Name)) fun acc name _ => do
    match env.getModuleIdxFor? name with
    | none => pure acc
    | some index =>
      if isProject env.header.moduleNames[index.toNat]! then pure (acc.push name) else pure acc
  let mut rejected : Array Name := #[]
  for name in declarations do
    let axioms ← collectAxioms name
    if axioms.any (fun ax => !allowed.contains ax) then
      rejected := rejected.push name
  let summary := Json.mkObj [
    ("collector", toJson "Lean.collectAxioms"),
    ("modules", toJson modules.size),
    ("declarations", toJson declarations.size),
    ("allowed_axioms", toJson (allowed.map Name.toString)),
    ("rejected", toJson (rejected.map Name.toString))]
  logInfo m!"SINGER_AXIOM_SUMMARY {summary.compress}"
  unless rejected.isEmpty do
    throwError m!"Nonstandard transitive axioms in declarations: {rejected.toList}"

-- The model and the Singer cycle
#print axioms SingerC3.singer_iterate_183
#print axioms SingerC3.singer_iterate_ne
#print axioms SingerC3.hgen_iterate_three
#print axioms SingerC3.hgen_no_fixed_point
#print axioms SingerC3.exists_ptN
#print axioms SingerC3.lineSet_lineVec

-- The witness (upper bound)
#print axioms SingerC3.witness_spec
#print axioms SingerC3.five_mem_admissibleCaps

-- The reduction to 61 orbit conditions
#print axioms SingerC3.ncard_inter_lineVec
#print axioms SingerC3.reduction
#print axioms SingerC3.cap_four_reduction

-- The kernel-checked search
#print axioms SingerC3.go_sound
#print axioms SingerC3.searchCut_sound
#print axioms SingerC3.Cert.noSol_root
#print axioms SingerC3.not_systemSolvable

-- Main statements
#print axioms SingerC3.no_invariant_cap_four
#print axioms SingerC3.exists_line_ge_five
#print axioms SingerC3.isLeast_admissibleCaps
