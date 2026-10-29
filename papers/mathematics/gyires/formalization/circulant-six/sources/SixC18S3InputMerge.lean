import SixC18S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC18S3InputPolynomial : Polynomial := SixC18S2OutputPolynomial
theorem SixC18S3Input_merge : orderedMerge 6188 SixC18S3InputLeftSorted SixC18S3InputRightSorted = SixC18S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC18S3Input_eval (f : ℕ →* ℝ) : eval f SixC18S3InputPolynomial = eval f (expandSlices 13 3 SixC18S3InputSlices) := by
  rw [← SixC18S3Input_merge, eval_orderedMerge, ← SixC18S3Input_left_sorted, ← SixC18S3Input_right_sorted, eval_sort, eval_sort, SixC18S3Input_flat, eval_append]
end SixCertificates
