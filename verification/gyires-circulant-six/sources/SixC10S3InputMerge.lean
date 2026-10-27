import SixC10S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC10S3InputPolynomial : Polynomial := SixC10S2OutputPolynomial
theorem SixC10S3Input_merge : orderedMerge 6188 SixC10S3InputLeftSorted SixC10S3InputRightSorted = SixC10S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC10S3Input_eval (f : ℕ →* ℝ) : eval f SixC10S3InputPolynomial = eval f (expandSlices 7 3 SixC10S3InputSlices) := by
  rw [← SixC10S3Input_merge, eval_orderedMerge, ← SixC10S3Input_left_sorted, ← SixC10S3Input_right_sorted, eval_sort, eval_sort, SixC10S3Input_flat, eval_append]
end SixCertificates
