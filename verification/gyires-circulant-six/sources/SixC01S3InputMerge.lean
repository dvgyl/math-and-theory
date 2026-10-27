import SixC01S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC01S3InputPolynomial : Polynomial := SixC01S2OutputPolynomial
theorem SixC01S3Input_merge : orderedMerge 6188 SixC01S3InputLeftSorted SixC01S3InputRightSorted = SixC01S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC01S3Input_eval (f : ℕ →* ℝ) : eval f SixC01S3InputPolynomial = eval f (expandSlices 5 3 SixC01S3InputSlices) := by
  rw [← SixC01S3Input_merge, eval_orderedMerge, ← SixC01S3Input_left_sorted, ← SixC01S3Input_right_sorted, eval_sort, eval_sort, SixC01S3Input_flat, eval_append]
end SixCertificates
