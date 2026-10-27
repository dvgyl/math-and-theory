import SixC40S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC40S0InputPolynomial : Polynomial := rawDense
theorem SixC40S0Input_merge : orderedMerge 6188 SixC40S0InputLeftSorted SixC40S0InputRightSorted = SixC40S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC40S0Input_eval (f : ℕ →* ℝ) : eval f SixC40S0InputPolynomial = eval f (expandSlices 7 3 SixC40S0InputSlices) := by
  rw [← SixC40S0Input_merge, eval_orderedMerge, ← SixC40S0Input_left_sorted, ← SixC40S0Input_right_sorted, eval_sort, eval_sort, SixC40S0Input_flat, eval_append]
end SixCertificates
