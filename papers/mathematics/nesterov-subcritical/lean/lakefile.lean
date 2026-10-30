import Lake
open Lake DSL
package nesterov_subcritical where
  leanOptions := #[⟨`warningAsError, true⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"
-- Every module of the tree is listed (the verification script checks this).
@[default_target] lean_lib NesterovSubcritical where
  roots := #[
    -- P: planar Huber valley model
    `RadialHuber, `ValleyModel,
    -- H: continuous-time Hilbert threshold
    `ConvexProjection, `PowerAlgebra, `PowerModel, `PowerNormal, `PowerEstimates,
    `PowerExterior, `ScalarModelBounds, `PowerValley, `PowerMinimizers, `ExponentSelection,
    `FiniteEuler, `ValleyPath, `FiniteExcursion, `MoreauTrajectory, `FiniteActual,
    `GeneralVolterraKernel, `GeneralVolterraOperator, `GeneralVolterraCalculus,
    `HilbertSum, `BlockScaling, `TimeScaling, `HilbertModel, `HilbertEscape, `HighDamping,
    `SharpThreshold, `LowDampingPotential, `LowDampingTrajectory, `LowDampingMain,
    `LowDampingHilbert, `AllPositiveThreshold,
    -- D: discrete-time threshold
    `NAGBasic, `NAGConjugacy, `NAGHilbertModel, `NAGVelocity, `NAGHilbertEscape,
    `NAGStability, `UniformTaylor, `NAGODELimit, `VolterraAcceleration, `NAGPlanarExcursion,
    `NAGDescent, `NAGHighDamping, `NAGAxisLift, `NAGLowDamping, `NAGLowHilbert,
    `NAGSharpThreshold,
    -- New: planar damping-r escape
    `PlanarEnergy, `EulerObstruction, `PlanarInvariants, `PlanarUnbounded,
    `PlanarTrajectory, `PlanarMain, `PlanarAllDamping,
    -- Merged audit
    `Audit]
