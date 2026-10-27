import SixC36S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC36S3InputPolynomial : Polynomial := SixC36S2OutputPolynomial
theorem SixC36S3Input_merge : orderedMerge 6188 SixC36S3InputLeftSorted SixC36S3InputRightSorted = SixC36S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC36S3Input_eval (f : ℕ →* ℝ) : eval f SixC36S3InputPolynomial = eval f (expandSlices 11 5 SixC36S3InputSlices) := by
  rw [← SixC36S3Input_merge, eval_orderedMerge, ← SixC36S3Input_left_sorted, ← SixC36S3Input_right_sorted, eval_sort, eval_sort, SixC36S3Input_flat, eval_append]
end SixCertificates
