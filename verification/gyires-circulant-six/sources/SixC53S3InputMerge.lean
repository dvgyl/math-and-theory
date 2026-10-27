import SixC53S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC53S3InputPolynomial : Polynomial := SixC53S2OutputPolynomial
theorem SixC53S3Input_merge : orderedMerge 6188 SixC53S3InputLeftSorted SixC53S3InputRightSorted = SixC53S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC53S3Input_eval (f : ℕ →* ℝ) : eval f SixC53S3InputPolynomial = eval f (expandSlices 3 7 SixC53S3InputSlices) := by
  rw [← SixC53S3Input_merge, eval_orderedMerge, ← SixC53S3Input_left_sorted, ← SixC53S3Input_right_sorted, eval_sort, eval_sort, SixC53S3Input_flat, eval_append]
end SixCertificates
