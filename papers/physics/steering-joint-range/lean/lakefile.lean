import Lake
open Lake DSL

package milne_bounds where
  moreLeanArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib MilneBounds where
  srcDir := "Lean"
  roots := #[
    `MilneDefs,
    `MilneBlochDefs,
    `MilneCore,
    `MilneQubit,
    `MilnePurityCovariance,
    `MilneCorrelation,
    `MilneGeometry,
    `MilneBlochIdentities,
    `MilneGeometryBridge,
    `MilneFiltering,
    `MilneCanonicalization,
    `MilneScalarBounds,
    `MilneSharpness,
    `MilneGeometrySharpness,
    `MilneSteering,
    `MilneSingular,
    `MilneAllStates,
    `MilneOptimality,
    `MilneNonattainment,
    `MilneRefinement,
    `MilneGeometryConsequences,
    `MilneGeometryRange,
    `MilneOrbitDiagonal,
    `MilneOrbitOrthogonal,
    `MilneOrbitSecular,
    `MilneOrbitPolynomial,
    `MilneOrbitSpectral,
    `MilneOrbitOpenBall,
    `MilneComplexFiltering,
    `MilneOneSided,
    `MilnePhysicalOrbit,
    `MilneQubitBall,
    `MilnePhysicalOrbitFilter,
    `MilneOrbitFullFilter,
    `MilneCenterCoordinates,
    `MilneCenterVerification,
    `MilneStabilityScalar,
    `MilneAlignedState,
    `MilneLocalUnitary,
    `MilneQubitDiagonalization,
    `MilneFractionSharpness,
    `MilneGeometryInterval,
    `MilneVolumeGeometry,
    `MilneVolumeSharpness,
    `MilneVolumeUnitary,
    `MilneCanonicalNormalForm,
    `MilneTraceNorm,
    `MilneAlignedStability,
    `MilneTraceDistance,
    `MilneCanonicalRigidity,
    `MilneKrausProbability,
    `MilneProbabilityScalar,
    `MilneProbabilityEnvelope,
    `MilneJointMinimum,
    `MilneJointMinimumPhysical,
    `MilneJointStability,
    `MilneJointPhysicalStability,
    `MilneJointSpectrum,
    `MilneJointArbitraryStability,
    `MilneFractionOptimality,
    `MilneVerification,
    `MilneGlobalRigidity,
    `MilneEndpointRigidity,
    `MilneAlignedEquality,
    `MilneBobRadialNormalForm,
    `MilneRigidityVerification,
    `MilneOrbitV2Verification,
    `MilneVolumePhysical,
    `MilneResearchVerification,
    `MilneReleaseVerification
  ]

/-- Whole-project transitive axiom audit (not a default target). -/
lean_lib MilneAudit where
  srcDir := "Lean"
  roots := #[`MilneAxiomAudit]
