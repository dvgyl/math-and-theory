import SixC59S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC59S3InputPolynomial : Polynomial := SixC59S2OutputPolynomial
theorem SixC59S3Input_merge : orderedMerge 6188 SixC59S3InputLeftSorted SixC59S3InputRightSorted = SixC59S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC59S3Input_eval (f : ℕ →* ℝ) : eval f SixC59S3InputPolynomial = eval f (expandSlices 5 7 SixC59S3InputSlices) := by
  rw [← SixC59S3Input_merge, eval_orderedMerge, ← SixC59S3Input_left_sorted, ← SixC59S3Input_right_sorted, eval_sort, eval_sort, SixC59S3Input_flat, eval_append]
end SixCertificates
