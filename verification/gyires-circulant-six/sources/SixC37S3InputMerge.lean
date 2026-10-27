import SixC37S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC37S3InputPolynomial : Polynomial := SixC37S2OutputPolynomial
theorem SixC37S3Input_merge : orderedMerge 6188 SixC37S3InputLeftSorted SixC37S3InputRightSorted = SixC37S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC37S3Input_eval (f : ℕ →* ℝ) : eval f SixC37S3InputPolynomial = eval f (expandSlices 11 5 SixC37S3InputSlices) := by
  rw [← SixC37S3Input_merge, eval_orderedMerge, ← SixC37S3Input_left_sorted, ← SixC37S3Input_right_sorted, eval_sort, eval_sort, SixC37S3Input_flat, eval_append]
end SixCertificates
