import SixC29S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC29S3InputPolynomial : Polynomial := SixC29S2OutputPolynomial
theorem SixC29S3Input_merge : orderedMerge 6188 SixC29S3InputLeftSorted SixC29S3InputRightSorted = SixC29S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC29S3Input_eval (f : ℕ →* ℝ) : eval f SixC29S3InputPolynomial = eval f (expandSlices 3 5 SixC29S3InputSlices) := by
  rw [← SixC29S3Input_merge, eval_orderedMerge, ← SixC29S3Input_left_sorted, ← SixC29S3Input_right_sorted, eval_sort, eval_sort, SixC29S3Input_flat, eval_append]
end SixCertificates
