import SixC19S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC19S3InputPolynomial : Polynomial := SixC19S2OutputPolynomial
theorem SixC19S3Input_merge : orderedMerge 6188 SixC19S3InputLeftSorted SixC19S3InputRightSorted = SixC19S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC19S3Input_eval (f : ℕ →* ℝ) : eval f SixC19S3InputPolynomial = eval f (expandSlices 13 3 SixC19S3InputSlices) := by
  rw [← SixC19S3Input_merge, eval_orderedMerge, ← SixC19S3Input_left_sorted, ← SixC19S3Input_right_sorted, eval_sort, eval_sort, SixC19S3Input_flat, eval_append]
end SixCertificates
