import SixC48S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC48S3InputPolynomial : Polynomial := SixC48S2OutputPolynomial
theorem SixC48S3Input_merge : orderedMerge 6188 SixC48S3InputLeftSorted SixC48S3InputRightSorted = SixC48S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC48S3Input_eval (f : ℕ →* ℝ) : eval f SixC48S3InputPolynomial = eval f (expandSlices 3 7 SixC48S3InputSlices) := by
  rw [← SixC48S3Input_merge, eval_orderedMerge, ← SixC48S3Input_left_sorted, ← SixC48S3Input_right_sorted, eval_sort, eval_sort, SixC48S3Input_flat, eval_append]
end SixCertificates
