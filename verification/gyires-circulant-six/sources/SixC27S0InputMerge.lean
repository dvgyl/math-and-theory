import SixC27S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC27S0InputPolynomial : Polynomial := rawDense
theorem SixC27S0Input_merge : orderedMerge 6188 SixC27S0InputLeftSorted SixC27S0InputRightSorted = SixC27S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC27S0Input_eval (f : ℕ →* ℝ) : eval f SixC27S0InputPolynomial = eval f (expandSlices 7 13 SixC27S0InputSlices) := by
  rw [← SixC27S0Input_merge, eval_orderedMerge, ← SixC27S0Input_left_sorted, ← SixC27S0Input_right_sorted, eval_sort, eval_sort, SixC27S0Input_flat, eval_append]
end SixCertificates
