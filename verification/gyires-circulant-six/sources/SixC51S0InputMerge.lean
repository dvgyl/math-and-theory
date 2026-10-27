import SixC51S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC51S0InputPolynomial : Polynomial := rawDense
theorem SixC51S0Input_merge : orderedMerge 6188 SixC51S0InputLeftSorted SixC51S0InputRightSorted = SixC51S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC51S0Input_eval (f : ℕ →* ℝ) : eval f SixC51S0InputPolynomial = eval f (expandSlices 5 13 SixC51S0InputSlices) := by
  rw [← SixC51S0Input_merge, eval_orderedMerge, ← SixC51S0Input_left_sorted, ← SixC51S0Input_right_sorted, eval_sort, eval_sort, SixC51S0Input_flat, eval_append]
end SixCertificates
