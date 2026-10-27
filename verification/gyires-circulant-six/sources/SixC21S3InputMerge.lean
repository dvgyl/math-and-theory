import SixC21S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC21S3InputPolynomial : Polynomial := SixC21S2OutputPolynomial
theorem SixC21S3Input_merge : orderedMerge 6188 SixC21S3InputLeftSorted SixC21S3InputRightSorted = SixC21S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC21S3Input_eval (f : ℕ →* ℝ) : eval f SixC21S3InputPolynomial = eval f (expandSlices 13 3 SixC21S3InputSlices) := by
  rw [← SixC21S3Input_merge, eval_orderedMerge, ← SixC21S3Input_left_sorted, ← SixC21S3Input_right_sorted, eval_sort, eval_sort, SixC21S3Input_flat, eval_append]
end SixCertificates
