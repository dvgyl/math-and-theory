import SixC50S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC50S3InputPolynomial : Polynomial := SixC50S2OutputPolynomial
theorem SixC50S3Input_merge : orderedMerge 6188 SixC50S3InputLeftSorted SixC50S3InputRightSorted = SixC50S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC50S3Input_eval (f : ℕ →* ℝ) : eval f SixC50S3InputPolynomial = eval f (expandSlices 3 7 SixC50S3InputSlices) := by
  rw [← SixC50S3Input_merge, eval_orderedMerge, ← SixC50S3Input_left_sorted, ← SixC50S3Input_right_sorted, eval_sort, eval_sort, SixC50S3Input_flat, eval_append]
end SixCertificates
