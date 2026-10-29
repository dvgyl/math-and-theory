import SixC16S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC16S3InputPolynomial : Polynomial := SixC16S2OutputPolynomial
theorem SixC16S3Input_merge : orderedMerge 6188 SixC16S3InputLeftSorted SixC16S3InputRightSorted = SixC16S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC16S3Input_eval (f : ℕ →* ℝ) : eval f SixC16S3InputPolynomial = eval f (expandSlices 11 3 SixC16S3InputSlices) := by
  rw [← SixC16S3Input_merge, eval_orderedMerge, ← SixC16S3Input_left_sorted, ← SixC16S3Input_right_sorted, eval_sort, eval_sort, SixC16S3Input_flat, eval_append]
end SixCertificates
