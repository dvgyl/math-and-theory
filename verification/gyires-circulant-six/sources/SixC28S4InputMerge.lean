import SixC28S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC28S4InputPolynomial : Polynomial := SixC28S3OutputPolynomial
theorem SixC28S4Input_merge : orderedMerge 6188 SixC28S4InputLeftSorted SixC28S4InputRightSorted = SixC28S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC28S4Input_eval (f : ℕ →* ℝ) : eval f SixC28S4InputPolynomial = eval f (expandSlices 5 2 SixC28S4InputSlices) := by
  rw [← SixC28S4Input_merge, eval_orderedMerge, ← SixC28S4Input_left_sorted, ← SixC28S4Input_right_sorted, eval_sort, eval_sort, SixC28S4Input_flat, eval_append]
end SixCertificates
