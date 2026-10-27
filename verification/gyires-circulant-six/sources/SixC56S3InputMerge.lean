import SixC56S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC56S3InputPolynomial : Polynomial := SixC56S2OutputPolynomial
theorem SixC56S3Input_merge : orderedMerge 6188 SixC56S3InputLeftSorted SixC56S3InputRightSorted = SixC56S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC56S3Input_eval (f : ℕ →* ℝ) : eval f SixC56S3InputPolynomial = eval f (expandSlices 5 7 SixC56S3InputSlices) := by
  rw [← SixC56S3Input_merge, eval_orderedMerge, ← SixC56S3Input_left_sorted, ← SixC56S3Input_right_sorted, eval_sort, eval_sort, SixC56S3Input_flat, eval_append]
end SixCertificates
