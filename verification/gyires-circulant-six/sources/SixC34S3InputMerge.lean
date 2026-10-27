import SixC34S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC34S3InputPolynomial : Polynomial := SixC34S2OutputPolynomial
theorem SixC34S3Input_merge : orderedMerge 6188 SixC34S3InputLeftSorted SixC34S3InputRightSorted = SixC34S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC34S3Input_eval (f : ℕ →* ℝ) : eval f SixC34S3InputPolynomial = eval f (expandSlices 7 5 SixC34S3InputSlices) := by
  rw [← SixC34S3Input_merge, eval_orderedMerge, ← SixC34S3Input_left_sorted, ← SixC34S3Input_right_sorted, eval_sort, eval_sort, SixC34S3Input_flat, eval_append]
end SixCertificates
