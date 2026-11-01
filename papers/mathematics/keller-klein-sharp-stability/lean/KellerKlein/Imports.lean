import Mathlib.Tactic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian

/-!
Shared analytic and tactic imports for the proof.  Listing the needed subject
areas avoids loading unrelated portions of Mathlib in every source module.
This module declares no mathematical constants or additional assumptions.
-/
