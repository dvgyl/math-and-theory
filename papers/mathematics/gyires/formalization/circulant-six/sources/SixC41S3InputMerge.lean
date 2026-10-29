import SixC41S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC41S3InputPolynomial : Polynomial := SixC41S2OutputPolynomial
theorem SixC41S3Input_merge : orderedMerge 6188 SixC41S3InputLeftSorted SixC41S3InputRightSorted = SixC41S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC41S3Input_eval (f : ℕ →* ℝ) : eval f SixC41S3InputPolynomial = eval f (expandSlices 11 5 SixC41S3InputSlices) := by
  rw [← SixC41S3Input_merge, eval_orderedMerge, ← SixC41S3Input_left_sorted, ← SixC41S3Input_right_sorted, eval_sort, eval_sort, SixC41S3Input_flat, eval_append]
end SixCertificates
