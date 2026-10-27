import SixC46S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC46S0InputPolynomial : Polynomial := rawDense
theorem SixC46S0Input_merge : orderedMerge 6188 SixC46S0InputLeftSorted SixC46S0InputRightSorted = SixC46S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC46S0Input_eval (f : ℕ →* ℝ) : eval f SixC46S0InputPolynomial = eval f (expandSlices 7 3 SixC46S0InputSlices) := by
  rw [← SixC46S0Input_merge, eval_orderedMerge, ← SixC46S0Input_left_sorted, ← SixC46S0Input_right_sorted, eval_sort, eval_sort, SixC46S0Input_flat, eval_append]
end SixCertificates
