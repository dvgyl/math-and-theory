import SixC50S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC50S0InputPolynomial : Polynomial := rawDense
theorem SixC50S0Input_merge : orderedMerge 6188 SixC50S0InputLeftSorted SixC50S0InputRightSorted = SixC50S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC50S0Input_eval (f : ℕ →* ℝ) : eval f SixC50S0InputPolynomial = eval f (expandSlices 13 5 SixC50S0InputSlices) := by
  rw [← SixC50S0Input_merge, eval_orderedMerge, ← SixC50S0Input_left_sorted, ← SixC50S0Input_right_sorted, eval_sort, eval_sort, SixC50S0Input_flat, eval_append]
end SixCertificates
