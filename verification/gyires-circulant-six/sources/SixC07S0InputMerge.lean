import SixC07S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC07S0InputPolynomial : Polynomial := rawDense
theorem SixC07S0Input_merge : orderedMerge 6188 SixC07S0InputLeftSorted SixC07S0InputRightSorted = SixC07S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC07S0Input_eval (f : ℕ →* ℝ) : eval f SixC07S0InputPolynomial = eval f (expandSlices 11 13 SixC07S0InputSlices) := by
  rw [← SixC07S0Input_merge, eval_orderedMerge, ← SixC07S0Input_left_sorted, ← SixC07S0Input_right_sorted, eval_sort, eval_sort, SixC07S0Input_flat, eval_append]
end SixCertificates
