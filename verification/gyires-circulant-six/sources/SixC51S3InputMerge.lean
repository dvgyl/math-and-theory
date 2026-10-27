import SixC51S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC51S3InputPolynomial : Polynomial := SixC51S2OutputPolynomial
theorem SixC51S3Input_merge : orderedMerge 6188 SixC51S3InputLeftSorted SixC51S3InputRightSorted = SixC51S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC51S3Input_eval (f : ℕ →* ℝ) : eval f SixC51S3InputPolynomial = eval f (expandSlices 3 7 SixC51S3InputSlices) := by
  rw [← SixC51S3Input_merge, eval_orderedMerge, ← SixC51S3Input_left_sorted, ← SixC51S3Input_right_sorted, eval_sort, eval_sort, SixC51S3Input_flat, eval_append]
end SixCertificates
