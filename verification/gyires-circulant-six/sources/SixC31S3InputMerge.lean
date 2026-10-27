import SixC31S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC31S3InputPolynomial : Polynomial := SixC31S2OutputPolynomial
theorem SixC31S3Input_merge : orderedMerge 6188 SixC31S3InputLeftSorted SixC31S3InputRightSorted = SixC31S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC31S3Input_eval (f : ℕ →* ℝ) : eval f SixC31S3InputPolynomial = eval f (expandSlices 7 5 SixC31S3InputSlices) := by
  rw [← SixC31S3Input_merge, eval_orderedMerge, ← SixC31S3Input_left_sorted, ← SixC31S3Input_right_sorted, eval_sort, eval_sort, SixC31S3Input_flat, eval_append]
end SixCertificates
