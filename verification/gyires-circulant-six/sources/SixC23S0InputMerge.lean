import SixC23S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC23S0InputPolynomial : Polynomial := rawDense
theorem SixC23S0Input_merge : orderedMerge 6188 SixC23S0InputLeftSorted SixC23S0InputRightSorted = SixC23S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC23S0Input_eval (f : ℕ →* ℝ) : eval f SixC23S0InputPolynomial = eval f (expandSlices 5 7 SixC23S0InputSlices) := by
  rw [← SixC23S0Input_merge, eval_orderedMerge, ← SixC23S0Input_left_sorted, ← SixC23S0Input_right_sorted, eval_sort, eval_sort, SixC23S0Input_flat, eval_append]
end SixCertificates
