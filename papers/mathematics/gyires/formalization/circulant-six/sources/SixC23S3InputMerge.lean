import SixC23S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC23S3InputPolynomial : Polynomial := SixC23S2OutputPolynomial
theorem SixC23S3Input_merge : orderedMerge 6188 SixC23S3InputLeftSorted SixC23S3InputRightSorted = SixC23S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC23S3Input_eval (f : ℕ →* ℝ) : eval f SixC23S3InputPolynomial = eval f (expandSlices 13 3 SixC23S3InputSlices) := by
  rw [← SixC23S3Input_merge, eval_orderedMerge, ← SixC23S3Input_left_sorted, ← SixC23S3Input_right_sorted, eval_sort, eval_sort, SixC23S3Input_flat, eval_append]
end SixCertificates
