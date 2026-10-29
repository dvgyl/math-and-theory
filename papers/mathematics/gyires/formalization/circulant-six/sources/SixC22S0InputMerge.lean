import SixC22S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC22S0InputPolynomial : Polynomial := rawDense
theorem SixC22S0Input_merge : orderedMerge 6188 SixC22S0InputLeftSorted SixC22S0InputRightSorted = SixC22S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC22S0Input_eval (f : ℕ →* ℝ) : eval f SixC22S0InputPolynomial = eval f (expandSlices 7 5 SixC22S0InputSlices) := by
  rw [← SixC22S0Input_merge, eval_orderedMerge, ← SixC22S0Input_left_sorted, ← SixC22S0Input_right_sorted, eval_sort, eval_sort, SixC22S0Input_flat, eval_append]
end SixCertificates
