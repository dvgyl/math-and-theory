import Lake
open Lake DSL

package steeringBounds where
  moreLeanArgs := #["-j1", "--trust=0"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "56a005855ea17e0b0958f73ec801ae140b0a1679"

@[default_target]
lean_lib MilneBounds where
  srcDir := "Lean"
  roots := #[
    `MilneDefs,
    `MilneCore,
    `MilneFiltering,
    `MilneCanonicalization,
    `MilneQubit,
    `MilnePurityCovariance,
    `MilneBlochDefs,
    `MilneCorrelation,
    `MilneScalarBounds,
    `MilneSteering,
    `MilneSingular,
    `MilneSharpness,
    `MilneFractionSharpness,
    `MilneAllStates,
    `MilneOptimality,
    `MilneNonattainment,
    `MilneFractionOptimality,
    `MilneVerification
  ]

lean_lib Challenge

lean_lib Solution
