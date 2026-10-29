import SixC32S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC32S3InputPolynomial : Polynomial := SixC32S2OutputPolynomial
theorem SixC32S3Input_merge : orderedMerge 6188 SixC32S3InputLeftSorted SixC32S3InputRightSorted = SixC32S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC32S3Input_eval (f : ℕ →* ℝ) : eval f SixC32S3InputPolynomial = eval f (expandSlices 7 5 SixC32S3InputSlices) := by
  rw [← SixC32S3Input_merge, eval_orderedMerge, ← SixC32S3Input_left_sorted, ← SixC32S3Input_right_sorted, eval_sort, eval_sort, SixC32S3Input_flat, eval_append]
end SixCertificates
