import SixC05S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC05S1InputPolynomial : Polynomial := SixC05S0OutputPolynomial
theorem SixC05S1Input_merge : orderedMerge 6188 SixC05S1InputLeftSorted SixC05S1InputRightSorted = SixC05S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC05S1Input_eval (f : ℕ →* ℝ) : eval f SixC05S1InputPolynomial = eval f (expandSlices 11 13 SixC05S1InputSlices) := by
  rw [← SixC05S1Input_merge, eval_orderedMerge, ← SixC05S1Input_left_sorted, ← SixC05S1Input_right_sorted, eval_sort, eval_sort, SixC05S1Input_flat, eval_append]
end SixCertificates
