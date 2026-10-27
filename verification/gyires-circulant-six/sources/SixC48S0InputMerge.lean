import SixC48S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC48S0InputPolynomial : Polynomial := rawDense
theorem SixC48S0Input_merge : orderedMerge 6188 SixC48S0InputLeftSorted SixC48S0InputRightSorted = SixC48S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC48S0Input_eval (f : ℕ →* ℝ) : eval f SixC48S0InputPolynomial = eval f (expandSlices 13 11 SixC48S0InputSlices) := by
  rw [← SixC48S0Input_merge, eval_orderedMerge, ← SixC48S0Input_left_sorted, ← SixC48S0Input_right_sorted, eval_sort, eval_sort, SixC48S0Input_flat, eval_append]
end SixCertificates
