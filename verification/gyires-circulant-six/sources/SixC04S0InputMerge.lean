import SixC04S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC04S0InputPolynomial : Polynomial := rawDense
theorem SixC04S0Input_merge : orderedMerge 6188 SixC04S0InputLeftSorted SixC04S0InputRightSorted = SixC04S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC04S0Input_eval (f : ℕ →* ℝ) : eval f SixC04S0InputPolynomial = eval f (expandSlices 11 7 SixC04S0InputSlices) := by
  rw [← SixC04S0Input_merge, eval_orderedMerge, ← SixC04S0Input_left_sorted, ← SixC04S0Input_right_sorted, eval_sort, eval_sort, SixC04S0Input_flat, eval_append]
end SixCertificates
