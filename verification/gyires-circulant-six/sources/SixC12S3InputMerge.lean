import SixC12S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC12S3InputPolynomial : Polynomial := SixC12S2OutputPolynomial
theorem SixC12S3Input_merge : orderedMerge 6188 SixC12S3InputLeftSorted SixC12S3InputRightSorted = SixC12S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC12S3Input_eval (f : ℕ →* ℝ) : eval f SixC12S3InputPolynomial = eval f (expandSlices 11 3 SixC12S3InputSlices) := by
  rw [← SixC12S3Input_merge, eval_orderedMerge, ← SixC12S3Input_left_sorted, ← SixC12S3Input_right_sorted, eval_sort, eval_sort, SixC12S3Input_flat, eval_append]
end SixCertificates
