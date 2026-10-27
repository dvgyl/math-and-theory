import SixC01S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC01S0InputPolynomial : Polynomial := rawDense
theorem SixC01S0Input_merge : orderedMerge 6188 SixC01S0InputLeftSorted SixC01S0InputRightSorted = SixC01S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC01S0Input_eval (f : ℕ →* ℝ) : eval f SixC01S0InputPolynomial = eval f (expandSlices 11 13 SixC01S0InputSlices) := by
  rw [← SixC01S0Input_merge, eval_orderedMerge, ← SixC01S0Input_left_sorted, ← SixC01S0Input_right_sorted, eval_sort, eval_sort, SixC01S0Input_flat, eval_append]
end SixCertificates
