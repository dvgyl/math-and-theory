import Lake
open Lake DSL

package keller_klein_sharp_stability where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c44e0c8ee63ca166450922a373c7409c5d26b00b"

/-- The 62 modules of the earlier small-coefficient package, byte for byte. -/
lean_lib KellerKlein

/-- Nine support-gap modules of the preceding expanded package that the
new development imports. -/
lean_lib SupportGap where
  srcDir := "support-gap"
  roots := #[`AdversarialCentralGap, `AdversarialFiniteMoments,
    `AdversarialRademacherMoments, `ExactSupportGapAlgebra, `ExactSupportGap,
    `ExactSupportGapEquality, `RootGapFibers, `GapLayerRigidity, `RootGapCore]

/-- The deterministic inverse, stability and modulus development. -/
@[default_target] lean_lib SharpStability where
  srcDir := "stability"
  roots := #[`GapMajoritySlice, `HypersimplexSharp, `GlobalGapRigidity,
    `GapRigidityExamples, `GapFlatStability, `RootSharpTail, `GapPhaseStability,
    `AllCapGapStability, `ActualGlobalGapStability, `RootModulusAlgebra,
    `RootTailModulus, `ExactSaturatedModulus, `ActualSaturatedModulus,
    `FixedFlatTradeoff, `SharpStabilityExamples]

/-- Actual attaining vectors for the exact saturated modulus. -/
@[default_target] lean_lib ModulusAttainment where
  srcDir := "attainment"
  roots := #[`ExactModulusAttainment]

/-- The conditional finite-law bridge; analytic tail inputs are hypotheses. -/
@[default_target] lean_lib FourShiftBridge where
  srcDir := "bridge"
  roots := #[`FourShiftLaw, `FourShiftEnvelope]
