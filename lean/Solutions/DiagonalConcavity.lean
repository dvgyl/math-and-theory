module
public import MathAndTheory.Mathematics.DiagonalConcavity
public section
namespace ConcavityChallenge
open MathAndTheory.DiagonalConcavity Set
theorem result {M : ℝ} (hM : 0 < M) :
    (ConcaveOn ℝ (Ioi 0) (fun t => rootedFamily M (fun _ => t)) ↔ 1 ≤ M) ∧
      (ConcaveOn ℝ positiveOrthant (rootedFamily M) ↔ M = 1) := by
  exact complete_classification hM
end ConcavityChallenge
#print axioms ConcavityChallenge.result
