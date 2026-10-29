import SixC43S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC43S3InputPolynomial : Polynomial := SixC43S2OutputPolynomial
theorem SixC43S3Input_merge : orderedMerge 6188 SixC43S3InputLeftSorted SixC43S3InputRightSorted = SixC43S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC43S3Input_eval (f : ℕ →* ℝ) : eval f SixC43S3InputPolynomial = eval f (expandSlices 13 5 SixC43S3InputSlices) := by
  rw [← SixC43S3Input_merge, eval_orderedMerge, ← SixC43S3Input_left_sorted, ← SixC43S3Input_right_sorted, eval_sort, eval_sort, SixC43S3Input_flat, eval_append]
end SixCertificates
