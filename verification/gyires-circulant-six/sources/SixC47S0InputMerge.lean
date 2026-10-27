import SixC47S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC47S0InputPolynomial : Polynomial := rawDense
theorem SixC47S0Input_merge : orderedMerge 6188 SixC47S0InputLeftSorted SixC47S0InputRightSorted = SixC47S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC47S0Input_eval (f : ℕ →* ℝ) : eval f SixC47S0InputPolynomial = eval f (expandSlices 3 7 SixC47S0InputSlices) := by
  rw [← SixC47S0Input_merge, eval_orderedMerge, ← SixC47S0Input_left_sorted, ← SixC47S0Input_right_sorted, eval_sort, eval_sort, SixC47S0Input_flat, eval_append]
end SixCertificates
