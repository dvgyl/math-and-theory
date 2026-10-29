import Lake
open Lake DSL

package milne_bounds where
  moreLeanArgs := #["-j1", "--trust=0", "-DwarningAsError=true"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "c44e0c8ee63ca166450922a373c7409c5d26b00b"

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
