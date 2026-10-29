import SixC28S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC28S0InputPolynomial : Polynomial := rawDense
theorem SixC28S0Input_merge : orderedMerge 6188 SixC28S0InputLeftSorted SixC28S0InputRightSorted = SixC28S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC28S0Input_eval (f : ℕ →* ℝ) : eval f SixC28S0InputPolynomial = eval f (expandSlices 11 7 SixC28S0InputSlices) := by
  rw [← SixC28S0Input_merge, eval_orderedMerge, ← SixC28S0Input_left_sorted, ← SixC28S0Input_right_sorted, eval_sort, eval_sort, SixC28S0Input_flat, eval_append]
end SixCertificates
