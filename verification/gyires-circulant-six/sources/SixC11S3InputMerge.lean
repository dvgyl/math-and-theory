import SixC11S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC11S3InputPolynomial : Polynomial := SixC11S2OutputPolynomial
theorem SixC11S3Input_merge : orderedMerge 6188 SixC11S3InputLeftSorted SixC11S3InputRightSorted = SixC11S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC11S3Input_eval (f : ℕ →* ℝ) : eval f SixC11S3InputPolynomial = eval f (expandSlices 7 3 SixC11S3InputSlices) := by
  rw [← SixC11S3Input_merge, eval_orderedMerge, ← SixC11S3Input_left_sorted, ← SixC11S3Input_right_sorted, eval_sort, eval_sort, SixC11S3Input_flat, eval_append]
end SixCertificates
