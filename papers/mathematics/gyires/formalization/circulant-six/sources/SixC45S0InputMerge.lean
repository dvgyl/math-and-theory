import SixC45S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC45S0InputPolynomial : Polynomial := rawDense
theorem SixC45S0Input_merge : orderedMerge 6188 SixC45S0InputLeftSorted SixC45S0InputRightSorted = SixC45S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC45S0Input_eval (f : ℕ →* ℝ) : eval f SixC45S0InputPolynomial = eval f (expandSlices 3 11 SixC45S0InputSlices) := by
  rw [← SixC45S0Input_merge, eval_orderedMerge, ← SixC45S0Input_left_sorted, ← SixC45S0Input_right_sorted, eval_sort, eval_sort, SixC45S0Input_flat, eval_append]
end SixCertificates
