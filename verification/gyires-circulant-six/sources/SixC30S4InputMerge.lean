import SixC30S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC30S4InputPolynomial : Polynomial := SixC30S3OutputPolynomial
theorem SixC30S4Input_merge : orderedMerge 6188 SixC30S4InputLeftSorted SixC30S4InputRightSorted = SixC30S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC30S4Input_eval (f : ℕ →* ℝ) : eval f SixC30S4InputPolynomial = eval f (expandSlices 5 2 SixC30S4InputSlices) := by
  rw [← SixC30S4Input_merge, eval_orderedMerge, ← SixC30S4Input_left_sorted, ← SixC30S4Input_right_sorted, eval_sort, eval_sort, SixC30S4Input_flat, eval_append]
end SixCertificates
