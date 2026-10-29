import SixC57S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC57S3InputPolynomial : Polynomial := SixC57S2OutputPolynomial
theorem SixC57S3Input_merge : orderedMerge 6188 SixC57S3InputLeftSorted SixC57S3InputRightSorted = SixC57S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC57S3Input_eval (f : ℕ →* ℝ) : eval f SixC57S3InputPolynomial = eval f (expandSlices 5 7 SixC57S3InputSlices) := by
  rw [← SixC57S3Input_merge, eval_orderedMerge, ← SixC57S3Input_left_sorted, ← SixC57S3Input_right_sorted, eval_sort, eval_sort, SixC57S3Input_flat, eval_append]
end SixCertificates
