import SixC05S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC05S4InputPolynomial : Polynomial := SixC05S3OutputPolynomial
theorem SixC05S4Input_merge : orderedMerge 6188 SixC05S4InputLeftSorted SixC05S4InputRightSorted = SixC05S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC05S4Input_eval (f : ℕ →* ℝ) : eval f SixC05S4InputPolynomial = eval f (expandSlices 3 2 SixC05S4InputSlices) := by
  rw [← SixC05S4Input_merge, eval_orderedMerge, ← SixC05S4Input_left_sorted, ← SixC05S4Input_right_sorted, eval_sort, eval_sort, SixC05S4Input_flat, eval_append]
end SixCertificates
