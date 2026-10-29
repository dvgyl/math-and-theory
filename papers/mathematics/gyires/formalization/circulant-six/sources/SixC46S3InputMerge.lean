import SixC46S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC46S3InputPolynomial : Polynomial := SixC46S2OutputPolynomial
theorem SixC46S3Input_merge : orderedMerge 6188 SixC46S3InputLeftSorted SixC46S3InputRightSorted = SixC46S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC46S3Input_eval (f : ℕ →* ℝ) : eval f SixC46S3InputPolynomial = eval f (expandSlices 13 5 SixC46S3InputSlices) := by
  rw [← SixC46S3Input_merge, eval_orderedMerge, ← SixC46S3Input_left_sorted, ← SixC46S3Input_right_sorted, eval_sort, eval_sort, SixC46S3Input_flat, eval_append]
end SixCertificates
