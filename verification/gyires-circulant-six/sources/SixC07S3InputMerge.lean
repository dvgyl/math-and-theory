import SixC07S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC07S3InputPolynomial : Polynomial := SixC07S2OutputPolynomial
theorem SixC07S3Input_merge : orderedMerge 6188 SixC07S3InputLeftSorted SixC07S3InputRightSorted = SixC07S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC07S3Input_eval (f : ℕ →* ℝ) : eval f SixC07S3InputPolynomial = eval f (expandSlices 7 3 SixC07S3InputSlices) := by
  rw [← SixC07S3Input_merge, eval_orderedMerge, ← SixC07S3Input_left_sorted, ← SixC07S3Input_right_sorted, eval_sort, eval_sort, SixC07S3Input_flat, eval_append]
end SixCertificates
