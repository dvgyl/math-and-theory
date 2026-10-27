import SixC35S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC35S3InputPolynomial : Polynomial := SixC35S2OutputPolynomial
theorem SixC35S3Input_merge : orderedMerge 6188 SixC35S3InputLeftSorted SixC35S3InputRightSorted = SixC35S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC35S3Input_eval (f : ℕ →* ℝ) : eval f SixC35S3InputPolynomial = eval f (expandSlices 7 5 SixC35S3InputSlices) := by
  rw [← SixC35S3Input_merge, eval_orderedMerge, ← SixC35S3Input_left_sorted, ← SixC35S3Input_right_sorted, eval_sort, eval_sort, SixC35S3Input_flat, eval_append]
end SixCertificates
