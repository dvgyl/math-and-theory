import SixC02S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC02S0InputPolynomial : Polynomial := rawDense
theorem SixC02S0Input_merge : orderedMerge 6188 SixC02S0InputLeftSorted SixC02S0InputRightSorted = SixC02S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC02S0Input_eval (f : ℕ →* ℝ) : eval f SixC02S0InputPolynomial = eval f (expandSlices 13 7 SixC02S0InputSlices) := by
  rw [← SixC02S0Input_merge, eval_orderedMerge, ← SixC02S0Input_left_sorted, ← SixC02S0Input_right_sorted, eval_sort, eval_sort, SixC02S0Input_flat, eval_append]
end SixCertificates
