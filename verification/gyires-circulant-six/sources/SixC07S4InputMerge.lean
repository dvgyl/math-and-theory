import SixC07S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC07S4InputPolynomial : Polynomial := SixC07S3OutputPolynomial
theorem SixC07S4Input_merge : orderedMerge 6188 SixC07S4InputLeftSorted SixC07S4InputRightSorted = SixC07S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC07S4Input_eval (f : ℕ →* ℝ) : eval f SixC07S4InputPolynomial = eval f (expandSlices 3 2 SixC07S4InputSlices) := by
  rw [← SixC07S4Input_merge, eval_orderedMerge, ← SixC07S4Input_left_sorted, ← SixC07S4Input_right_sorted, eval_sort, eval_sort, SixC07S4Input_flat, eval_append]
end SixCertificates
