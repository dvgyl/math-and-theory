import SixC28S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC28S3InputPolynomial : Polynomial := SixC28S2OutputPolynomial
theorem SixC28S3Input_merge : orderedMerge 6188 SixC28S3InputLeftSorted SixC28S3InputRightSorted = SixC28S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC28S3Input_eval (f : ℕ →* ℝ) : eval f SixC28S3InputPolynomial = eval f (expandSlices 3 5 SixC28S3InputSlices) := by
  rw [← SixC28S3Input_merge, eval_orderedMerge, ← SixC28S3Input_left_sorted, ← SixC28S3Input_right_sorted, eval_sort, eval_sort, SixC28S3Input_flat, eval_append]
end SixCertificates
