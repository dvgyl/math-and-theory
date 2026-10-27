import SixC32S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC32S0InputPolynomial : Polynomial := rawDense
theorem SixC32S0Input_merge : orderedMerge 6188 SixC32S0InputLeftSorted SixC32S0InputRightSorted = SixC32S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC32S0Input_eval (f : ℕ →* ℝ) : eval f SixC32S0InputPolynomial = eval f (expandSlices 13 3 SixC32S0InputSlices) := by
  rw [← SixC32S0Input_merge, eval_orderedMerge, ← SixC32S0Input_left_sorted, ← SixC32S0Input_right_sorted, eval_sort, eval_sort, SixC32S0Input_flat, eval_append]
end SixCertificates
