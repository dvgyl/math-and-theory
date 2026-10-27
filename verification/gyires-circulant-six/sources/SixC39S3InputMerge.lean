import SixC39S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC39S3InputPolynomial : Polynomial := SixC39S2OutputPolynomial
theorem SixC39S3Input_merge : orderedMerge 6188 SixC39S3InputLeftSorted SixC39S3InputRightSorted = SixC39S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC39S3Input_eval (f : ℕ →* ℝ) : eval f SixC39S3InputPolynomial = eval f (expandSlices 11 5 SixC39S3InputSlices) := by
  rw [← SixC39S3Input_merge, eval_orderedMerge, ← SixC39S3Input_left_sorted, ← SixC39S3Input_right_sorted, eval_sort, eval_sort, SixC39S3Input_flat, eval_append]
end SixCertificates
