import SixC37S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC37S0InputPolynomial : Polynomial := rawDense
theorem SixC37S0Input_merge : orderedMerge 6188 SixC37S0InputLeftSorted SixC37S0InputRightSorted = SixC37S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC37S0Input_eval (f : ℕ →* ℝ) : eval f SixC37S0InputPolynomial = eval f (expandSlices 7 13 SixC37S0InputSlices) := by
  rw [← SixC37S0Input_merge, eval_orderedMerge, ← SixC37S0Input_left_sorted, ← SixC37S0Input_right_sorted, eval_sort, eval_sort, SixC37S0Input_flat, eval_append]
end SixCertificates
