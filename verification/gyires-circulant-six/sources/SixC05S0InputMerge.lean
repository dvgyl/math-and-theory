import SixC05S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC05S0InputPolynomial : Polynomial := rawDense
theorem SixC05S0Input_merge : orderedMerge 6188 SixC05S0InputLeftSorted SixC05S0InputRightSorted = SixC05S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC05S0Input_eval (f : ℕ →* ℝ) : eval f SixC05S0InputPolynomial = eval f (expandSlices 7 11 SixC05S0InputSlices) := by
  rw [← SixC05S0Input_merge, eval_orderedMerge, ← SixC05S0Input_left_sorted, ← SixC05S0Input_right_sorted, eval_sort, eval_sort, SixC05S0Input_flat, eval_append]
end SixCertificates
