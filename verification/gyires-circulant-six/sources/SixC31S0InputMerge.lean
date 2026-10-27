import SixC31S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC31S0InputPolynomial : Polynomial := rawDense
theorem SixC31S0Input_merge : orderedMerge 6188 SixC31S0InputLeftSorted SixC31S0InputRightSorted = SixC31S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC31S0Input_eval (f : ℕ →* ℝ) : eval f SixC31S0InputPolynomial = eval f (expandSlices 11 13 SixC31S0InputSlices) := by
  rw [← SixC31S0Input_merge, eval_orderedMerge, ← SixC31S0Input_left_sorted, ← SixC31S0Input_right_sorted, eval_sort, eval_sort, SixC31S0Input_flat, eval_append]
end SixCertificates
