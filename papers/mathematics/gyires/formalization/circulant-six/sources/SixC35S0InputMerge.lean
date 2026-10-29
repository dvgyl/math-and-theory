import SixC35S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC35S0InputPolynomial : Polynomial := rawDense
theorem SixC35S0Input_merge : orderedMerge 6188 SixC35S0InputLeftSorted SixC35S0InputRightSorted = SixC35S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC35S0Input_eval (f : ℕ →* ℝ) : eval f SixC35S0InputPolynomial = eval f (expandSlices 3 11 SixC35S0InputSlices) := by
  rw [← SixC35S0Input_merge, eval_orderedMerge, ← SixC35S0Input_left_sorted, ← SixC35S0Input_right_sorted, eval_sort, eval_sort, SixC35S0Input_flat, eval_append]
end SixCertificates
