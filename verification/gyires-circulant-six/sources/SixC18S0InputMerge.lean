import SixC18S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC18S0InputPolynomial : Polynomial := rawDense
theorem SixC18S0Input_merge : orderedMerge 6188 SixC18S0InputLeftSorted SixC18S0InputRightSorted = SixC18S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC18S0Input_eval (f : ℕ →* ℝ) : eval f SixC18S0InputPolynomial = eval f (expandSlices 11 7 SixC18S0InputSlices) := by
  rw [← SixC18S0Input_merge, eval_orderedMerge, ← SixC18S0Input_left_sorted, ← SixC18S0Input_right_sorted, eval_sort, eval_sort, SixC18S0Input_flat, eval_append]
end SixCertificates
