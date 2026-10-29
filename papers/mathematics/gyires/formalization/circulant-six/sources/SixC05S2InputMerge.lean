import SixC05S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC05S2InputPolynomial : Polynomial := SixC05S1OutputPolynomial
theorem SixC05S2Input_merge : orderedMerge 6188 SixC05S2InputLeftSorted SixC05S2InputRightSorted = SixC05S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC05S2Input_eval (f : ℕ →* ℝ) : eval f SixC05S2InputPolynomial = eval f (expandSlices 13 5 SixC05S2InputSlices) := by
  rw [← SixC05S2Input_merge, eval_orderedMerge, ← SixC05S2Input_left_sorted, ← SixC05S2Input_right_sorted, eval_sort, eval_sort, SixC05S2Input_flat, eval_append]
end SixCertificates
