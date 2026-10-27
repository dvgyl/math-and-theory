import SixC55S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC55S3InputPolynomial : Polynomial := SixC55S2OutputPolynomial
theorem SixC55S3Input_merge : orderedMerge 6188 SixC55S3InputLeftSorted SixC55S3InputRightSorted = SixC55S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC55S3Input_eval (f : ℕ →* ℝ) : eval f SixC55S3InputPolynomial = eval f (expandSlices 5 7 SixC55S3InputSlices) := by
  rw [← SixC55S3Input_merge, eval_orderedMerge, ← SixC55S3Input_left_sorted, ← SixC55S3Input_right_sorted, eval_sort, eval_sort, SixC55S3Input_flat, eval_append]
end SixCertificates
