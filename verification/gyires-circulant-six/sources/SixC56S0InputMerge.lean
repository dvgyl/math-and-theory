import SixC56S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC56S0InputPolynomial : Polynomial := rawDense
theorem SixC56S0Input_merge : orderedMerge 6188 SixC56S0InputLeftSorted SixC56S0InputRightSorted = SixC56S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC56S0Input_eval (f : ℕ →* ℝ) : eval f SixC56S0InputPolynomial = eval f (expandSlices 13 3 SixC56S0InputSlices) := by
  rw [← SixC56S0Input_merge, eval_orderedMerge, ← SixC56S0Input_left_sorted, ← SixC56S0Input_right_sorted, eval_sort, eval_sort, SixC56S0Input_flat, eval_append]
end SixCertificates
