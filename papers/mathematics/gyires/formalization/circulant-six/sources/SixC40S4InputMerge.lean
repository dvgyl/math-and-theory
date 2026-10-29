import SixC40S4InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC40S4InputPolynomial : Polynomial := SixC40S3OutputPolynomial
theorem SixC40S4Input_merge : orderedMerge 6188 SixC40S4InputLeftSorted SixC40S4InputRightSorted = SixC40S4InputPolynomial := by apply same_sound; decide +kernel
theorem SixC40S4Input_eval (f : ℕ →* ℝ) : eval f SixC40S4InputPolynomial = eval f (expandSlices 5 2 SixC40S4InputSlices) := by
  rw [← SixC40S4Input_merge, eval_orderedMerge, ← SixC40S4Input_left_sorted, ← SixC40S4Input_right_sorted, eval_sort, eval_sort, SixC40S4Input_flat, eval_append]
end SixCertificates
