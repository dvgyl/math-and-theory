import SixC13S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC13S3InputPolynomial : Polynomial := SixC13S2OutputPolynomial
theorem SixC13S3Input_merge : orderedMerge 6188 SixC13S3InputLeftSorted SixC13S3InputRightSorted = SixC13S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC13S3Input_eval (f : ℕ →* ℝ) : eval f SixC13S3InputPolynomial = eval f (expandSlices 11 3 SixC13S3InputSlices) := by
  rw [← SixC13S3Input_merge, eval_orderedMerge, ← SixC13S3Input_left_sorted, ← SixC13S3Input_right_sorted, eval_sort, eval_sort, SixC13S3Input_flat, eval_append]
end SixCertificates
