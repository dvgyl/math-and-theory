import SixC59S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC59S0InputPolynomial : Polynomial := rawDense
theorem SixC59S0Input_merge : orderedMerge 6188 SixC59S0InputLeftSorted SixC59S0InputRightSorted = SixC59S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC59S0Input_eval (f : ℕ →* ℝ) : eval f SixC59S0InputPolynomial = eval f (expandSlices 3 11 SixC59S0InputSlices) := by
  rw [← SixC59S0Input_merge, eval_orderedMerge, ← SixC59S0Input_left_sorted, ← SixC59S0Input_right_sorted, eval_sort, eval_sort, SixC59S0Input_flat, eval_append]
end SixCertificates
