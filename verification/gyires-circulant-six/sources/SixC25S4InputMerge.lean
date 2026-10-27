import SixC25S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC25S4InputPolynomial : Polynomial := SixC25S3OutputPolynomial
theorem SixC25S4Input_merge : orderedMerge 6188 SixC25S4InputLeftSorted SixC25S4InputRightSorted = SixC25S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC25S4Input_eval (f : ℕ →* ℝ) : eval f SixC25S4InputPolynomial = eval f (expandSlices 5 2 SixC25S4InputSlices) := by
  rw [← SixC25S4Input_merge, eval_orderedMerge, ← SixC25S4Input_left_sorted, ← SixC25S4Input_right_sorted, eval_sort, eval_sort, SixC25S4Input_flat, eval_append]
end SixCertificates
