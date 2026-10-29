import SixC58S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC58S3InputPolynomial : Polynomial := SixC58S2OutputPolynomial
theorem SixC58S3Input_merge : orderedMerge 6188 SixC58S3InputLeftSorted SixC58S3InputRightSorted = SixC58S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC58S3Input_eval (f : ℕ →* ℝ) : eval f SixC58S3InputPolynomial = eval f (expandSlices 5 7 SixC58S3InputSlices) := by
  rw [← SixC58S3Input_merge, eval_orderedMerge, ← SixC58S3Input_left_sorted, ← SixC58S3Input_right_sorted, eval_sort, eval_sort, SixC58S3Input_flat, eval_append]
end SixCertificates
