import SixC30S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC30S0InputPolynomial : Polynomial := rawDense
theorem SixC30S0Input_merge : orderedMerge 6188 SixC30S0InputLeftSorted SixC30S0InputRightSorted = SixC30S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC30S0Input_eval (f : ℕ →* ℝ) : eval f SixC30S0InputPolynomial = eval f (expandSlices 13 11 SixC30S0InputSlices) := by
  rw [← SixC30S0Input_merge, eval_orderedMerge, ← SixC30S0Input_left_sorted, ← SixC30S0Input_right_sorted, eval_sort, eval_sort, SixC30S0Input_flat, eval_append]
end SixCertificates
