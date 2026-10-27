import SixC40S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC40S3InputPolynomial : Polynomial := SixC40S2OutputPolynomial
theorem SixC40S3Input_merge : orderedMerge 6188 SixC40S3InputLeftSorted SixC40S3InputRightSorted = SixC40S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC40S3Input_eval (f : ℕ →* ℝ) : eval f SixC40S3InputPolynomial = eval f (expandSlices 11 5 SixC40S3InputSlices) := by
  rw [← SixC40S3Input_merge, eval_orderedMerge, ← SixC40S3Input_left_sorted, ← SixC40S3Input_right_sorted, eval_sort, eval_sort, SixC40S3Input_flat, eval_append]
end SixCertificates
