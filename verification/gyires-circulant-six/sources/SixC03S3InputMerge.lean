import SixC03S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC03S3InputPolynomial : Polynomial := SixC03S2OutputPolynomial
theorem SixC03S3Input_merge : orderedMerge 6188 SixC03S3InputLeftSorted SixC03S3InputRightSorted = SixC03S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC03S3Input_eval (f : ℕ →* ℝ) : eval f SixC03S3InputPolynomial = eval f (expandSlices 5 3 SixC03S3InputSlices) := by
  rw [← SixC03S3Input_merge, eval_orderedMerge, ← SixC03S3Input_left_sorted, ← SixC03S3Input_right_sorted, eval_sort, eval_sort, SixC03S3Input_flat, eval_append]
end SixCertificates
