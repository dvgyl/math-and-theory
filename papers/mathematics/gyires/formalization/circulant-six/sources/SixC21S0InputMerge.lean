import SixC21S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC21S0InputPolynomial : Polynomial := rawDense
theorem SixC21S0Input_merge : orderedMerge 6188 SixC21S0InputLeftSorted SixC21S0InputRightSorted = SixC21S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC21S0Input_eval (f : ℕ →* ℝ) : eval f SixC21S0InputPolynomial = eval f (expandSlices 5 11 SixC21S0InputSlices) := by
  rw [← SixC21S0Input_merge, eval_orderedMerge, ← SixC21S0Input_left_sorted, ← SixC21S0Input_right_sorted, eval_sort, eval_sort, SixC21S0Input_flat, eval_append]
end SixCertificates
