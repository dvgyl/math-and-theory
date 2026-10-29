import SixC55S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC55S0InputPolynomial : Polynomial := rawDense
theorem SixC55S0Input_merge : orderedMerge 6188 SixC55S0InputLeftSorted SixC55S0InputRightSorted = SixC55S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC55S0Input_eval (f : ℕ →* ℝ) : eval f SixC55S0InputPolynomial = eval f (expandSlices 11 13 SixC55S0InputSlices) := by
  rw [← SixC55S0Input_merge, eval_orderedMerge, ← SixC55S0Input_left_sorted, ← SixC55S0Input_right_sorted, eval_sort, eval_sort, SixC55S0Input_flat, eval_append]
end SixCertificates
