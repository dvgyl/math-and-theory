import SixC26S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC26S0InputPolynomial : Polynomial := rawDense
theorem SixC26S0Input_merge : orderedMerge 6188 SixC26S0InputLeftSorted SixC26S0InputRightSorted = SixC26S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC26S0Input_eval (f : ℕ →* ℝ) : eval f SixC26S0InputPolynomial = eval f (expandSlices 13 7 SixC26S0InputSlices) := by
  rw [← SixC26S0Input_merge, eval_orderedMerge, ← SixC26S0Input_left_sorted, ← SixC26S0Input_right_sorted, eval_sort, eval_sort, SixC26S0Input_flat, eval_append]
end SixCertificates
