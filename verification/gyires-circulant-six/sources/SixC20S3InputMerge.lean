import SixC20S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC20S3InputPolynomial : Polynomial := SixC20S2OutputPolynomial
theorem SixC20S3Input_merge : orderedMerge 6188 SixC20S3InputLeftSorted SixC20S3InputRightSorted = SixC20S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC20S3Input_eval (f : ℕ →* ℝ) : eval f SixC20S3InputPolynomial = eval f (expandSlices 13 3 SixC20S3InputSlices) := by
  rw [← SixC20S3Input_merge, eval_orderedMerge, ← SixC20S3Input_left_sorted, ← SixC20S3Input_right_sorted, eval_sort, eval_sort, SixC20S3Input_flat, eval_append]
end SixCertificates
