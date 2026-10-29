import SixC39S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC39S0InputPolynomial : Polynomial := rawDense
theorem SixC39S0Input_merge : orderedMerge 6188 SixC39S0InputLeftSorted SixC39S0InputRightSorted = SixC39S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC39S0Input_eval (f : ℕ →* ℝ) : eval f SixC39S0InputPolynomial = eval f (expandSlices 3 13 SixC39S0InputSlices) := by
  rw [← SixC39S0Input_merge, eval_orderedMerge, ← SixC39S0Input_left_sorted, ← SixC39S0Input_right_sorted, eval_sort, eval_sort, SixC39S0Input_flat, eval_append]
end SixCertificates
