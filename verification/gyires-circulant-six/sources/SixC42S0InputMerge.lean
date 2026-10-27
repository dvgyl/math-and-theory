import SixC42S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC42S0InputPolynomial : Polynomial := rawDense
theorem SixC42S0Input_merge : orderedMerge 6188 SixC42S0InputLeftSorted SixC42S0InputRightSorted = SixC42S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC42S0Input_eval (f : ℕ →* ℝ) : eval f SixC42S0InputPolynomial = eval f (expandSlices 11 7 SixC42S0InputSlices) := by
  rw [← SixC42S0Input_merge, eval_orderedMerge, ← SixC42S0Input_left_sorted, ← SixC42S0Input_right_sorted, eval_sort, eval_sort, SixC42S0Input_flat, eval_append]
end SixCertificates
