import SixC06S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC06S3InputPolynomial : Polynomial := SixC06S2OutputPolynomial
theorem SixC06S3Input_merge : orderedMerge 6188 SixC06S3InputLeftSorted SixC06S3InputRightSorted = SixC06S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC06S3Input_eval (f : ℕ →* ℝ) : eval f SixC06S3InputPolynomial = eval f (expandSlices 7 3 SixC06S3InputSlices) := by
  rw [← SixC06S3Input_merge, eval_orderedMerge, ← SixC06S3Input_left_sorted, ← SixC06S3Input_right_sorted, eval_sort, eval_sort, SixC06S3Input_flat, eval_append]
end SixCertificates
