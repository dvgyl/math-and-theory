import Lake
open Lake DSL

package quantumExactContraction where
  moreLeanArgs := #["--trust=0", "-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib QuantumContractionProof where
  roots := #[`AuditExactContraction, `PalomarEndpoints]
  globs := #[
    .one `SpectralEntropy,
    .one `ADChannel,
    .one `TraceNormBounds,
    .one `ADSharp,
    .one `FlagBlocks,
    .one `ConditionalHockey,
    .one `GeneralKraus,
    .one `KrausSaturation,
    .one `KrausChannelSaturation,
    .one `GeneralContraction,
    .one `ReplacerBounds,
    .one `NegativeDepolarizingChannel,
    .one `PauliChannel,
    .one `CoefficientConvexity,
    .one `NegativeDepolarizingEffects,
    .one `NegativeDepolarizingDuality,
    .one `NegativeDepolarizingBounds,
    .one `KrausSupport,
    .one `BellSupport,
    .one `NegativeDepolarizingSharp,
    .one `ChannelKraus,
    .one `PositiveReplacerSDP,
    .one `NegativeDepolarizingDoeblin,
    .one `SimplexPreparation,
    .one `PhaseTransport,
    .one `UniversalContraction,
    .one `ContractionClassification,
    .one `NegativeDepolarizingExact,
    .one `PauliConditionalUpper,
    .one `PauliConditionalLower,
    .one `UnitaryCoefficient,
    .one `PauliSymmetry,
    .one `PauliMinimumPair,
    .one `PauliConditionalExact,
    .one `PauliDoeblin,
    .one `TightFrameGeometry,
    .one `TightFrameDual,
    .one `TightFrameColumns,
    .one `TightFramePairing,
    .one `TightFrameWitness,
    .one `BellEncoding,
    .one `DepolarizingEffectScalars,
    .one `DepolarizingWitnessScalars,
    .one `DepolarizingSharp,
    .one `WeylBell,
    .one `WeylFrame,
    .one `DepolarizingReduction,
    .one `DepolarizingChannel,
    .one `DepolarizingEffects,
    .one `DepolarizingBounds,
    .one `DepolarizingClosedBounds,
    .one `DepolarizingComparison,
    .one `PositiveDepolarizing,
    .one `FullDepolarizingChannel,
    .one `DepolarizingExact,
    .one `AuditExactContraction,
    .one `PalomarEndpoints]

lean_lib Challenge

lean_lib Solution

lean_lib PalomarAudit
