import SixC40S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC40S1InputPolynomial : Polynomial := SixC40S0OutputPolynomial
theorem SixC40S1Input_merge : orderedMerge 6188 SixC40S1InputLeftSorted SixC40S1InputRightSorted = SixC40S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC40S1Input_eval (f : ℕ →* ℝ) : eval f SixC40S1InputPolynomial = eval f (expandSlices 3 13 SixC40S1InputSlices) := by
  rw [← SixC40S1Input_merge, eval_orderedMerge, ← SixC40S1Input_left_sorted, ← SixC40S1Input_right_sorted, eval_sort, eval_sort, SixC40S1Input_flat, eval_append]
end SixCertificates
