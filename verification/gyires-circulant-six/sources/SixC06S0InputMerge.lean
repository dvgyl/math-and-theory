import SixC06S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC06S0InputPolynomial : Polynomial := rawDense
theorem SixC06S0Input_merge : orderedMerge 6188 SixC06S0InputLeftSorted SixC06S0InputRightSorted = SixC06S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC06S0Input_eval (f : ℕ →* ℝ) : eval f SixC06S0InputPolynomial = eval f (expandSlices 13 11 SixC06S0InputSlices) := by
  rw [← SixC06S0Input_merge, eval_orderedMerge, ← SixC06S0Input_left_sorted, ← SixC06S0Input_right_sorted, eval_sort, eval_sort, SixC06S0Input_flat, eval_append]
end SixCertificates
