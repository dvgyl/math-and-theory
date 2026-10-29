module
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public section
noncomputable section
open Set
namespace MathAndTheory.DiagonalConcavity
abbrev V4 := Fin 4 → ℝ

@[expose] def sigma1 (x : V4) : ℝ := x 0 + x 1 + x 2 + x 3
@[expose] def sigma2 (x : V4) : ℝ :=
  x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3
@[expose] def sigma3 (x : V4) : ℝ :=
  x 0 * x 1 * x 2 + x 0 * x 1 * x 3 + x 0 * x 2 * x 3 + x 1 * x 2 * x 3
@[expose] def sigma4 (x : V4) : ℝ := x 0 * x 1 * x 2 * x 3

@[expose] def family (M : ℝ) (x : V4) : ℝ :=
  1 + M * sigma1 x + sigma2 x + M * sigma3 x + sigma4 x

@[expose] def positiveOrthant : Set V4 := {x | ∀ i, 0 < x i}
@[expose] def fourthRoot (a : ℝ) : ℝ := a ^ (1 / 4 : ℝ)
@[expose] def rootedFamily (M : ℝ) (x : V4) : ℝ := fourthRoot (family M x)

end MathAndTheory.DiagonalConcavity

namespace ConcavityChallenge
open MathAndTheory.DiagonalConcavity Set
theorem result {M : ℝ} (hM : 0 < M) :
    (ConcaveOn ℝ (Ioi 0) (fun t => rootedFamily M (fun _ => t)) ↔ 1 ≤ M) ∧
      (ConcaveOn ℝ positiveOrthant (rootedFamily M) ↔ M = 1) := by
  sorry
end ConcavityChallenge
