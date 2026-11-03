import MilneDefs
import MilneBlochDefs
import MilneCore
import MilneQubit
import MilnePurityCovariance
import MilneCorrelation
import MilneGeometry
import MilneBlochIdentities
import MilneGeometryBridge
import MilneFiltering
import MilneCanonicalization
import MilneScalarBounds
import MilneSharpness
import MilneGeometrySharpness
import MilneSteering
import MilneSingular
import MilneAllStates
import MilneOptimality
import MilneNonattainment
import MilneRefinement
import MilneGeometryConsequences
import MilneGeometryRange
import MilneOrbitDiagonal
import MilneOrbitOrthogonal
import MilneOrbitSecular
import MilneOrbitPolynomial
import MilneOrbitSpectral
import MilneOrbitOpenBall
import MilneComplexFiltering
import MilneOneSided
import MilnePhysicalOrbit
import MilneQubitBall
import MilnePhysicalOrbitFilter
import MilneOrbitFullFilter
import MilneCenterCoordinates
import MilneCenterVerification
import MilneStabilityScalar
import MilneAlignedState
import MilneLocalUnitary
import MilneQubitDiagonalization
import MilneFractionSharpness
import MilneGeometryInterval
import MilneVolumeGeometry
import MilneVolumeSharpness
import MilneVolumeUnitary
import MilneCanonicalNormalForm
import MilneTraceNorm
import MilneAlignedStability
import MilneTraceDistance
import MilneCanonicalRigidity
import MilneKrausProbability
import MilneProbabilityScalar
import MilneProbabilityEnvelope
import MilneJointMinimum
import MilneJointMinimumPhysical
import MilneJointStability
import MilneJointPhysicalStability
import MilneJointSpectrum
import MilneJointArbitraryStability
import MilneFractionOptimality
import MilneVerification
import MilneGlobalRigidity
import MilneEndpointRigidity
import MilneAlignedEquality
import MilneBobRadialNormalForm
import MilneRigidityVerification
import MilneOrbitV2Verification
import MilneVolumePhysical
import MilneResearchVerification
import MilneReleaseVerification
import Lean.Util.CollectAxioms

/-!
Complete transitive axiom audit of all declarations owned by the seventy
project modules listed in `modules.txt`. Selection uses the defining module, not a list of public theorem names.
Private helpers and compiler-generated declarations are therefore included.
The collector is the same Lean utility used by `#print axioms`.

Lean 4.19's code generator also stores auxiliary declarations in the
environment: intermediate representations (`_cstage1`, `_cstage2`),
specializations (`_spec_k`), lifted lambdas (`_elambda_k`, `_lambda_k`),
closed-term extractions (`_closed_k`) and boxed or reduced-arity variants
(`_boxed`, `_rarg`). They are recorded as code-generation auxiliaries. Such an
auxiliary may depend only on the three standard axioms, on the code
generator's placeholder `lcProof` and on other code-generation auxiliaries.
Every other declaration must be a non-axiom depending only on `propext`,
`Classical.choice` and `Quot.sound`; so no theorem or definition outside the
auxiliaries depends on `lcProof` or on an auxiliary axiom.

Some project modules only print axiom reports for imported theorems and own
no declarations; their count is zero, and the Python checker confirms from
the source that they contain no declaration keywords.
-/

/-- Whether a name is a code-generation auxiliary of the Lean 4.19 compiler. -/
def Milne.Audit.isCodegenAuxiliary (name : Lean.Name) : Bool :=
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
  let modules : Array Name := #[
    `MilneDefs, `MilneBlochDefs, `MilneCore, `MilneQubit,
    `MilnePurityCovariance, `MilneCorrelation, `MilneGeometry,
    `MilneBlochIdentities, `MilneGeometryBridge, `MilneFiltering,
    `MilneCanonicalization, `MilneScalarBounds, `MilneSharpness,
    `MilneGeometrySharpness, `MilneSteering, `MilneSingular, `MilneAllStates,
    `MilneOptimality, `MilneNonattainment, `MilneRefinement,
    `MilneGeometryConsequences, `MilneGeometryRange, `MilneOrbitDiagonal,
    `MilneOrbitOrthogonal, `MilneOrbitSecular, `MilneOrbitPolynomial,
    `MilneOrbitSpectral, `MilneOrbitOpenBall, `MilneComplexFiltering,
    `MilneOneSided, `MilnePhysicalOrbit, `MilneQubitBall,
    `MilnePhysicalOrbitFilter, `MilneOrbitFullFilter,
    `MilneCenterCoordinates, `MilneCenterVerification, `MilneStabilityScalar,
    `MilneAlignedState, `MilneLocalUnitary, `MilneQubitDiagonalization,
    `MilneFractionSharpness, `MilneGeometryInterval, `MilneVolumeGeometry,
    `MilneVolumeSharpness, `MilneVolumeUnitary, `MilneCanonicalNormalForm,
    `MilneTraceNorm, `MilneAlignedStability, `MilneTraceDistance,
    `MilneCanonicalRigidity, `MilneKrausProbability, `MilneProbabilityScalar,
    `MilneProbabilityEnvelope, `MilneJointMinimum,
    `MilneJointMinimumPhysical, `MilneJointStability,
    `MilneJointPhysicalStability, `MilneJointSpectrum,
    `MilneJointArbitraryStability, `MilneFractionOptimality,
    `MilneVerification, `MilneGlobalRigidity, `MilneEndpointRigidity,
    `MilneAlignedEquality, `MilneBobRadialNormalForm,
    `MilneRigidityVerification, `MilneOrbitV2Verification,
    `MilneVolumePhysical, `MilneResearchVerification,
    `MilneReleaseVerification]
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
    let auxiliary := Milne.Audit.isCodegenAuxiliary name
    if auxiliary then
      auxiliaries := auxiliaries + 1
      if axioms.any (fun ax => !(allowed.contains ax || ax == `lcProof ||
          Milne.Audit.isCodegenAuxiliary ax)) then
        rejected := rejected.push name
    else if kind == "axiom" || axioms.any (fun ax => !allowed.contains ax) then
      rejected := rejected.push name
    let record := Json.mkObj [
      ("module", toJson owner.toString),
      ("name", toJson name.toString),
      ("kind", toJson kind),
      ("codegen_auxiliary", toJson auxiliary),
      ("axioms", toJson (axioms.map Name.toString))]
    logInfo m!"OPT_B_AXIOM_DECL {record.compress}"
  let mut counts : List (String × Json) := []
  for moduleName in modules do
    let count := (declarations.filter (fun entry => entry.1 == moduleName)).size
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
  logInfo m!"OPT_B_AXIOM_SUMMARY {summary.compress}"
  unless rejected.isEmpty do
    throwError m!"Nonstandard transitive axioms in declarations: {rejected.toList}"

