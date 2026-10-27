import SixC59S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC59S4InputPolynomial : Polynomial := SixC59S3OutputPolynomial
theorem SixC59S4Input_merge : orderedMerge 6188 SixC59S4InputLeftSorted SixC59S4InputRightSorted = SixC59S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC59S4Input_eval (f : ℕ →* ℝ) : eval f SixC59S4InputPolynomial = eval f (expandSlices 7 2 SixC59S4InputSlices) := by
  rw [← SixC59S4Input_merge, eval_orderedMerge, ← SixC59S4Input_left_sorted, ← SixC59S4Input_right_sorted, eval_sort, eval_sort, SixC59S4Input_flat, eval_append]
end SixCertificates
