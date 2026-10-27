import SixC25S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC25S3InputPolynomial : Polynomial := SixC25S2OutputPolynomial
theorem SixC25S3Input_merge : orderedMerge 6188 SixC25S3InputLeftSorted SixC25S3InputRightSorted = SixC25S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC25S3Input_eval (f : ℕ →* ℝ) : eval f SixC25S3InputPolynomial = eval f (expandSlices 3 5 SixC25S3InputSlices) := by
  rw [← SixC25S3Input_merge, eval_orderedMerge, ← SixC25S3Input_left_sorted, ← SixC25S3Input_right_sorted, eval_sort, eval_sort, SixC25S3Input_flat, eval_append]
end SixCertificates
