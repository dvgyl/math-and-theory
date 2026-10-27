import SixC45S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC45S4InputPolynomial : Polynomial := SixC45S3OutputPolynomial
theorem SixC45S4Input_merge : orderedMerge 6188 SixC45S4InputLeftSorted SixC45S4InputRightSorted = SixC45S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC45S4Input_eval (f : ℕ →* ℝ) : eval f SixC45S4InputPolynomial = eval f (expandSlices 5 2 SixC45S4InputSlices) := by
  rw [← SixC45S4Input_merge, eval_orderedMerge, ← SixC45S4Input_left_sorted, ← SixC45S4Input_right_sorted, eval_sort, eval_sort, SixC45S4Input_flat, eval_append]
end SixCertificates
