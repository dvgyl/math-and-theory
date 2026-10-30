import Lake
open Lake DSL

package pdhg_cycles_verification where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"

@[default_target]
lean_lib PDHGCycles where
  roots := #[`Proximal, `ThreeCycleThreshold, `ThreeCycleFunctions, `GeneralSteps, `TriangleCycle, `ParameterBoundary, `PhaseDiagram, `QuadraticStability, `FiniteCycle, `SevenCycle, `AttractingCycle, `SevenAttracting, `TrigSupport, `TrigGrid, `FourierModes, `FourierAlgebra, `FourierCertificates, `FourierSums, `FourierRobustness, `AsymptoticParameters, `AsymptoticCycle]
