import SixC36S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC36S0InputPolynomial : Polynomial := rawDense
theorem SixC36S0Input_merge : orderedMerge 6188 SixC36S0InputLeftSorted SixC36S0InputRightSorted = SixC36S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC36S0Input_eval (f : ℕ →* ℝ) : eval f SixC36S0InputPolynomial = eval f (expandSlices 13 7 SixC36S0InputSlices) := by
  rw [← SixC36S0Input_merge, eval_orderedMerge, ← SixC36S0Input_left_sorted, ← SixC36S0Input_right_sorted, eval_sort, eval_sort, SixC36S0Input_flat, eval_append]
end SixCertificates
