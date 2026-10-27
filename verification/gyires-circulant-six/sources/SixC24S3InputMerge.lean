import SixC24S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC24S3InputPolynomial : Polynomial := SixC24S2OutputPolynomial
theorem SixC24S3Input_merge : orderedMerge 6188 SixC24S3InputLeftSorted SixC24S3InputRightSorted = SixC24S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC24S3Input_eval (f : ℕ →* ℝ) : eval f SixC24S3InputPolynomial = eval f (expandSlices 3 5 SixC24S3InputSlices) := by
  rw [← SixC24S3Input_merge, eval_orderedMerge, ← SixC24S3Input_left_sorted, ← SixC24S3Input_right_sorted, eval_sort, eval_sort, SixC24S3Input_flat, eval_append]
end SixCertificates
