import SixC33S3InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC33S3InputPolynomial : Polynomial := SixC33S2OutputPolynomial
theorem SixC33S3Input_merge : orderedMerge 6188 SixC33S3InputLeftSorted SixC33S3InputRightSorted = SixC33S3InputPolynomial := by apply same_sound; decide +kernel
theorem SixC33S3Input_eval (f : ℕ →* ℝ) : eval f SixC33S3InputPolynomial = eval f (expandSlices 7 5 SixC33S3InputSlices) := by
  rw [← SixC33S3Input_merge, eval_orderedMerge, ← SixC33S3Input_left_sorted, ← SixC33S3Input_right_sorted, eval_sort, eval_sort, SixC33S3Input_flat, eval_append]
end SixCertificates
