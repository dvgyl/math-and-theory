import SixC15S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC15S0InputPolynomial : Polynomial := rawDense
theorem SixC15S0Input_merge : orderedMerge 6188 SixC15S0InputLeftSorted SixC15S0InputRightSorted = SixC15S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC15S0Input_eval (f : ℕ →* ℝ) : eval f SixC15S0InputPolynomial = eval f (expandSlices 5 13 SixC15S0InputSlices) := by
  rw [← SixC15S0Input_merge, eval_orderedMerge, ← SixC15S0Input_left_sorted, ← SixC15S0Input_right_sorted, eval_sort, eval_sort, SixC15S0Input_flat, eval_append]
end SixCertificates
