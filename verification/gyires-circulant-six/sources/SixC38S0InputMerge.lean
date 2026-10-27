import SixC38S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC38S0InputPolynomial : Polynomial := rawDense
theorem SixC38S0Input_merge : orderedMerge 6188 SixC38S0InputLeftSorted SixC38S0InputRightSorted = SixC38S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC38S0Input_eval (f : ℕ →* ℝ) : eval f SixC38S0InputPolynomial = eval f (expandSlices 13 3 SixC38S0InputSlices) := by
  rw [← SixC38S0Input_merge, eval_orderedMerge, ← SixC38S0Input_left_sorted, ← SixC38S0Input_right_sorted, eval_sort, eval_sort, SixC38S0Input_flat, eval_append]
end SixCertificates
