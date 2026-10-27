import SixC09S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC09S3InputPolynomial : Polynomial := SixC09S2OutputPolynomial
theorem SixC09S3Input_merge : orderedMerge 6188 SixC09S3InputLeftSorted SixC09S3InputRightSorted = SixC09S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC09S3Input_eval (f : ℕ →* ℝ) : eval f SixC09S3InputPolynomial = eval f (expandSlices 7 3 SixC09S3InputSlices) := by
  rw [← SixC09S3Input_merge, eval_orderedMerge, ← SixC09S3Input_left_sorted, ← SixC09S3Input_right_sorted, eval_sort, eval_sort, SixC09S3Input_flat, eval_append]
end SixCertificates
