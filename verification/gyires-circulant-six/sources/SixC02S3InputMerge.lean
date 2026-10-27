import SixC02S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC02S3InputPolynomial : Polynomial := SixC02S2OutputPolynomial
theorem SixC02S3Input_merge : orderedMerge 6188 SixC02S3InputLeftSorted SixC02S3InputRightSorted = SixC02S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC02S3Input_eval (f : ℕ →* ℝ) : eval f SixC02S3InputPolynomial = eval f (expandSlices 5 3 SixC02S3InputSlices) := by
  rw [← SixC02S3Input_merge, eval_orderedMerge, ← SixC02S3Input_left_sorted, ← SixC02S3Input_right_sorted, eval_sort, eval_sort, SixC02S3Input_flat, eval_append]
end SixCertificates
