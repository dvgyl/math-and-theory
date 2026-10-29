import SixC42S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC42S3InputPolynomial : Polynomial := SixC42S2OutputPolynomial
theorem SixC42S3Input_merge : orderedMerge 6188 SixC42S3InputLeftSorted SixC42S3InputRightSorted = SixC42S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC42S3Input_eval (f : ℕ →* ℝ) : eval f SixC42S3InputPolynomial = eval f (expandSlices 13 5 SixC42S3InputSlices) := by
  rw [← SixC42S3Input_merge, eval_orderedMerge, ← SixC42S3Input_left_sorted, ← SixC42S3Input_right_sorted, eval_sort, eval_sort, SixC42S3Input_flat, eval_append]
end SixCertificates
