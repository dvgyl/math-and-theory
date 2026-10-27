import SixC41S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC41S4InputPolynomial : Polynomial := SixC41S3OutputPolynomial
theorem SixC41S4Input_merge : orderedMerge 6188 SixC41S4InputLeftSorted SixC41S4InputRightSorted = SixC41S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC41S4Input_eval (f : ℕ →* ℝ) : eval f SixC41S4InputPolynomial = eval f (expandSlices 5 2 SixC41S4InputSlices) := by
  rw [← SixC41S4Input_merge, eval_orderedMerge, ← SixC41S4Input_left_sorted, ← SixC41S4Input_right_sorted, eval_sort, eval_sort, SixC41S4Input_flat, eval_append]
end SixCertificates
