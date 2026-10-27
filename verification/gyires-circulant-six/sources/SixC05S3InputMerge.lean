import SixC05S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC05S3InputPolynomial : Polynomial := SixC05S2OutputPolynomial
theorem SixC05S3Input_merge : orderedMerge 6188 SixC05S3InputLeftSorted SixC05S3InputRightSorted = SixC05S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC05S3Input_eval (f : ℕ →* ℝ) : eval f SixC05S3InputPolynomial = eval f (expandSlices 5 3 SixC05S3InputSlices) := by
  rw [← SixC05S3Input_merge, eval_orderedMerge, ← SixC05S3Input_left_sorted, ← SixC05S3Input_right_sorted, eval_sort, eval_sort, SixC05S3Input_flat, eval_append]
end SixCertificates
