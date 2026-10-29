import SixC15S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC15S3InputPolynomial : Polynomial := SixC15S2OutputPolynomial
theorem SixC15S3Input_merge : orderedMerge 6188 SixC15S3InputLeftSorted SixC15S3InputRightSorted = SixC15S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC15S3Input_eval (f : ℕ →* ℝ) : eval f SixC15S3InputPolynomial = eval f (expandSlices 11 3 SixC15S3InputSlices) := by
  rw [← SixC15S3Input_merge, eval_orderedMerge, ← SixC15S3Input_left_sorted, ← SixC15S3Input_right_sorted, eval_sort, eval_sort, SixC15S3Input_flat, eval_append]
end SixCertificates
