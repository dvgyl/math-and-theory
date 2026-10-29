import SixC08S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC08S3InputPolynomial : Polynomial := SixC08S2OutputPolynomial
theorem SixC08S3Input_merge : orderedMerge 6188 SixC08S3InputLeftSorted SixC08S3InputRightSorted = SixC08S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC08S3Input_eval (f : ℕ →* ℝ) : eval f SixC08S3InputPolynomial = eval f (expandSlices 7 3 SixC08S3InputSlices) := by
  rw [← SixC08S3Input_merge, eval_orderedMerge, ← SixC08S3Input_left_sorted, ← SixC08S3Input_right_sorted, eval_sort, eval_sort, SixC08S3Input_flat, eval_append]
end SixCertificates
