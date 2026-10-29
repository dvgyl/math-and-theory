import SixC22S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC22S3InputPolynomial : Polynomial := SixC22S2OutputPolynomial
theorem SixC22S3Input_merge : orderedMerge 6188 SixC22S3InputLeftSorted SixC22S3InputRightSorted = SixC22S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC22S3Input_eval (f : ℕ →* ℝ) : eval f SixC22S3InputPolynomial = eval f (expandSlices 13 3 SixC22S3InputSlices) := by
  rw [← SixC22S3Input_merge, eval_orderedMerge, ← SixC22S3Input_left_sorted, ← SixC22S3Input_right_sorted, eval_sort, eval_sort, SixC22S3Input_flat, eval_append]
end SixCertificates
