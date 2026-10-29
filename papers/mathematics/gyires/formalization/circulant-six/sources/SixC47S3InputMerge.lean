import SixC47S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC47S3InputPolynomial : Polynomial := SixC47S2OutputPolynomial
theorem SixC47S3Input_merge : orderedMerge 6188 SixC47S3InputLeftSorted SixC47S3InputRightSorted = SixC47S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC47S3Input_eval (f : ℕ →* ℝ) : eval f SixC47S3InputPolynomial = eval f (expandSlices 13 5 SixC47S3InputSlices) := by
  rw [← SixC47S3Input_merge, eval_orderedMerge, ← SixC47S3Input_left_sorted, ← SixC47S3Input_right_sorted, eval_sort, eval_sort, SixC47S3Input_flat, eval_append]
end SixCertificates
