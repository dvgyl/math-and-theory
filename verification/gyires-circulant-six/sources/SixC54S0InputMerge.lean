import SixC54S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC54S0InputPolynomial : Polynomial := rawDense
theorem SixC54S0Input_merge : orderedMerge 6188 SixC54S0InputLeftSorted SixC54S0InputRightSorted = SixC54S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC54S0Input_eval (f : ℕ →* ℝ) : eval f SixC54S0InputPolynomial = eval f (expandSlices 13 11 SixC54S0InputSlices) := by
  rw [← SixC54S0Input_merge, eval_orderedMerge, ← SixC54S0Input_left_sorted, ← SixC54S0Input_right_sorted, eval_sort, eval_sort, SixC54S0Input_flat, eval_append]
end SixCertificates
