import SixC38S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC38S3InputPolynomial : Polynomial := SixC38S2OutputPolynomial
theorem SixC38S3Input_merge : orderedMerge 6188 SixC38S3InputLeftSorted SixC38S3InputRightSorted = SixC38S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC38S3Input_eval (f : ℕ →* ℝ) : eval f SixC38S3InputPolynomial = eval f (expandSlices 11 5 SixC38S3InputSlices) := by
  rw [← SixC38S3Input_merge, eval_orderedMerge, ← SixC38S3Input_left_sorted, ← SixC38S3Input_right_sorted, eval_sort, eval_sort, SixC38S3Input_flat, eval_append]
end SixCertificates
