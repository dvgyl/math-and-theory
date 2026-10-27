import SixC17S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC17S3InputPolynomial : Polynomial := SixC17S2OutputPolynomial
theorem SixC17S3Input_merge : orderedMerge 6188 SixC17S3InputLeftSorted SixC17S3InputRightSorted = SixC17S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC17S3Input_eval (f : ℕ →* ℝ) : eval f SixC17S3InputPolynomial = eval f (expandSlices 11 3 SixC17S3InputSlices) := by
  rw [← SixC17S3Input_merge, eval_orderedMerge, ← SixC17S3Input_left_sorted, ← SixC17S3Input_right_sorted, eval_sort, eval_sort, SixC17S3Input_flat, eval_append]
end SixCertificates
