import SixC41S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC41S0InputPolynomial : Polynomial := rawDense
theorem SixC41S0Input_merge : orderedMerge 6188 SixC41S0InputLeftSorted SixC41S0InputRightSorted = SixC41S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC41S0Input_eval (f : ℕ →* ℝ) : eval f SixC41S0InputPolynomial = eval f (expandSlices 3 7 SixC41S0InputSlices) := by
  rw [← SixC41S0Input_merge, eval_orderedMerge, ← SixC41S0Input_left_sorted, ← SixC41S0Input_right_sorted, eval_sort, eval_sort, SixC41S0Input_flat, eval_append]
end SixCertificates
