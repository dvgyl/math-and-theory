import SixC52S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC52S0InputPolynomial : Polynomial := rawDense
theorem SixC52S0Input_merge : orderedMerge 6188 SixC52S0InputLeftSorted SixC52S0InputRightSorted = SixC52S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC52S0Input_eval (f : ℕ →* ℝ) : eval f SixC52S0InputPolynomial = eval f (expandSlices 11 5 SixC52S0InputSlices) := by
  rw [← SixC52S0Input_merge, eval_orderedMerge, ← SixC52S0Input_left_sorted, ← SixC52S0Input_right_sorted, eval_sort, eval_sort, SixC52S0Input_flat, eval_append]
end SixCertificates
