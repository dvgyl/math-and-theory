import SixC44S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC44S3InputPolynomial : Polynomial := SixC44S2OutputPolynomial
theorem SixC44S3Input_merge : orderedMerge 6188 SixC44S3InputLeftSorted SixC44S3InputRightSorted = SixC44S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC44S3Input_eval (f : ℕ →* ℝ) : eval f SixC44S3InputPolynomial = eval f (expandSlices 13 5 SixC44S3InputSlices) := by
  rw [← SixC44S3Input_merge, eval_orderedMerge, ← SixC44S3Input_left_sorted, ← SixC44S3Input_right_sorted, eval_sort, eval_sort, SixC44S3Input_flat, eval_append]
end SixCertificates
