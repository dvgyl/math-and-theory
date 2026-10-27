import SixC30S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC30S3InputPolynomial : Polynomial := SixC30S2OutputPolynomial
theorem SixC30S3Input_merge : orderedMerge 6188 SixC30S3InputLeftSorted SixC30S3InputRightSorted = SixC30S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC30S3Input_eval (f : ℕ →* ℝ) : eval f SixC30S3InputPolynomial = eval f (expandSlices 7 5 SixC30S3InputSlices) := by
  rw [← SixC30S3Input_merge, eval_orderedMerge, ← SixC30S3Input_left_sorted, ← SixC30S3Input_right_sorted, eval_sort, eval_sort, SixC30S3Input_flat, eval_append]
end SixCertificates
