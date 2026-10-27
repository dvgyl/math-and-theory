import SixC49S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC49S3InputPolynomial : Polynomial := SixC49S2OutputPolynomial
theorem SixC49S3Input_merge : orderedMerge 6188 SixC49S3InputLeftSorted SixC49S3InputRightSorted = SixC49S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC49S3Input_eval (f : ℕ →* ℝ) : eval f SixC49S3InputPolynomial = eval f (expandSlices 3 7 SixC49S3InputSlices) := by
  rw [← SixC49S3Input_merge, eval_orderedMerge, ← SixC49S3Input_left_sorted, ← SixC49S3Input_right_sorted, eval_sort, eval_sort, SixC49S3Input_flat, eval_append]
end SixCertificates
