import SixC44S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC44S4InputPolynomial : Polynomial := SixC44S3OutputPolynomial
theorem SixC44S4Input_merge : orderedMerge 6188 SixC44S4InputLeftSorted SixC44S4InputRightSorted = SixC44S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC44S4Input_eval (f : ℕ →* ℝ) : eval f SixC44S4InputPolynomial = eval f (expandSlices 5 2 SixC44S4InputSlices) := by
  rw [← SixC44S4Input_merge, eval_orderedMerge, ← SixC44S4Input_left_sorted, ← SixC44S4Input_right_sorted, eval_sort, eval_sort, SixC44S4Input_flat, eval_append]
end SixCertificates
