import SixC27S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC27S3InputPolynomial : Polynomial := SixC27S2OutputPolynomial
theorem SixC27S3Input_merge : orderedMerge 6188 SixC27S3InputLeftSorted SixC27S3InputRightSorted = SixC27S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC27S3Input_eval (f : ℕ →* ℝ) : eval f SixC27S3InputPolynomial = eval f (expandSlices 3 5 SixC27S3InputSlices) := by
  rw [← SixC27S3Input_merge, eval_orderedMerge, ← SixC27S3Input_left_sorted, ← SixC27S3Input_right_sorted, eval_sort, eval_sort, SixC27S3Input_flat, eval_append]
end SixCertificates
