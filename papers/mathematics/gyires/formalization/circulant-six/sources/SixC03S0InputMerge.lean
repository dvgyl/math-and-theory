import SixC03S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC03S0InputPolynomial : Polynomial := rawDense
theorem SixC03S0Input_merge : orderedMerge 6188 SixC03S0InputLeftSorted SixC03S0InputRightSorted = SixC03S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC03S0Input_eval (f : ℕ →* ℝ) : eval f SixC03S0InputPolynomial = eval f (expandSlices 7 13 SixC03S0InputSlices) := by
  rw [← SixC03S0Input_merge, eval_orderedMerge, ← SixC03S0Input_left_sorted, ← SixC03S0Input_right_sorted, eval_sort, eval_sort, SixC03S0Input_flat, eval_append]
end SixCertificates
