import SixC57S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC57S0InputPolynomial : Polynomial := rawDense
theorem SixC57S0Input_merge : orderedMerge 6188 SixC57S0InputLeftSorted SixC57S0InputRightSorted = SixC57S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC57S0Input_eval (f : ℕ →* ℝ) : eval f SixC57S0InputPolynomial = eval f (expandSlices 3 13 SixC57S0InputSlices) := by
  rw [← SixC57S0Input_merge, eval_orderedMerge, ← SixC57S0Input_left_sorted, ← SixC57S0Input_right_sorted, eval_sort, eval_sort, SixC57S0Input_flat, eval_append]
end SixCertificates
