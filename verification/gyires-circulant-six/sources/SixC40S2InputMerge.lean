import SixC40S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC40S2InputPolynomial : Polynomial := SixC40S1OutputPolynomial
theorem SixC40S2Input_merge : orderedMerge 6188 SixC40S2InputLeftSorted SixC40S2InputRightSorted = SixC40S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC40S2Input_eval (f : ℕ →* ℝ) : eval f SixC40S2InputPolynomial = eval f (expandSlices 13 11 SixC40S2InputSlices) := by
  rw [← SixC40S2Input_merge, eval_orderedMerge, ← SixC40S2Input_left_sorted, ← SixC40S2Input_right_sorted, eval_sort, eval_sort, SixC40S2Input_flat, eval_append]
end SixCertificates
