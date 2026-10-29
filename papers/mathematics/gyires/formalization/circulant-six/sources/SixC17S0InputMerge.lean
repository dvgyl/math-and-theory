import SixC17S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC17S0InputPolynomial : Polynomial := rawDense
theorem SixC17S0Input_merge : orderedMerge 6188 SixC17S0InputLeftSorted SixC17S0InputRightSorted = SixC17S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC17S0Input_eval (f : ℕ →* ℝ) : eval f SixC17S0InputPolynomial = eval f (expandSlices 5 7 SixC17S0InputSlices) := by
  rw [← SixC17S0Input_merge, eval_orderedMerge, ← SixC17S0Input_left_sorted, ← SixC17S0Input_right_sorted, eval_sort, eval_sort, SixC17S0Input_flat, eval_append]
end SixCertificates
