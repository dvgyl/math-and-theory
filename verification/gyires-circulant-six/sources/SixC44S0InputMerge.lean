import SixC44S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC44S0InputPolynomial : Polynomial := rawDense
theorem SixC44S0Input_merge : orderedMerge 6188 SixC44S0InputLeftSorted SixC44S0InputRightSorted = SixC44S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC44S0Input_eval (f : ℕ →* ℝ) : eval f SixC44S0InputPolynomial = eval f (expandSlices 11 3 SixC44S0InputSlices) := by
  rw [← SixC44S0Input_merge, eval_orderedMerge, ← SixC44S0Input_left_sorted, ← SixC44S0Input_right_sorted, eval_sort, eval_sort, SixC44S0Input_flat, eval_append]
end SixCertificates
