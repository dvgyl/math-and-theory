import SixC52S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC52S3InputPolynomial : Polynomial := SixC52S2OutputPolynomial
theorem SixC52S3Input_merge : orderedMerge 6188 SixC52S3InputLeftSorted SixC52S3InputRightSorted = SixC52S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC52S3Input_eval (f : ℕ →* ℝ) : eval f SixC52S3InputPolynomial = eval f (expandSlices 3 7 SixC52S3InputSlices) := by
  rw [← SixC52S3Input_merge, eval_orderedMerge, ← SixC52S3Input_left_sorted, ← SixC52S3Input_right_sorted, eval_sort, eval_sort, SixC52S3Input_flat, eval_append]
end SixCertificates
