import SixC09S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC09S0InputPolynomial : Polynomial := rawDense
theorem SixC09S0Input_merge : orderedMerge 6188 SixC09S0InputLeftSorted SixC09S0InputRightSorted = SixC09S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC09S0Input_eval (f : ℕ →* ℝ) : eval f SixC09S0InputPolynomial = eval f (expandSlices 5 13 SixC09S0InputSlices) := by
  rw [← SixC09S0Input_merge, eval_orderedMerge, ← SixC09S0Input_left_sorted, ← SixC09S0Input_right_sorted, eval_sort, eval_sort, SixC09S0Input_flat, eval_append]
end SixCertificates
