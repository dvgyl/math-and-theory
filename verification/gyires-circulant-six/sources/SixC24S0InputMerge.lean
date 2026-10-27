import SixC24S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC24S0InputPolynomial : Polynomial := rawDense
theorem SixC24S0Input_merge : orderedMerge 6188 SixC24S0InputLeftSorted SixC24S0InputRightSorted = SixC24S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC24S0Input_eval (f : ℕ →* ℝ) : eval f SixC24S0InputPolynomial = eval f (expandSlices 13 11 SixC24S0InputSlices) := by
  rw [← SixC24S0Input_merge, eval_orderedMerge, ← SixC24S0Input_left_sorted, ← SixC24S0Input_right_sorted, eval_sort, eval_sort, SixC24S0Input_flat, eval_append]
end SixCertificates
