import SixC26S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC26S3InputPolynomial : Polynomial := SixC26S2OutputPolynomial
theorem SixC26S3Input_merge : orderedMerge 6188 SixC26S3InputLeftSorted SixC26S3InputRightSorted = SixC26S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC26S3Input_eval (f : ℕ →* ℝ) : eval f SixC26S3InputPolynomial = eval f (expandSlices 3 5 SixC26S3InputSlices) := by
  rw [← SixC26S3Input_merge, eval_orderedMerge, ← SixC26S3Input_left_sorted, ← SixC26S3Input_right_sorted, eval_sort, eval_sort, SixC26S3Input_flat, eval_append]
end SixCertificates
