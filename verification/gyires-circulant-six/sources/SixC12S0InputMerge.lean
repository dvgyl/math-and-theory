import SixC12S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC12S0InputPolynomial : Polynomial := rawDense
theorem SixC12S0Input_merge : orderedMerge 6188 SixC12S0InputLeftSorted SixC12S0InputRightSorted = SixC12S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC12S0Input_eval (f : ℕ →* ℝ) : eval f SixC12S0InputPolynomial = eval f (expandSlices 13 7 SixC12S0InputSlices) := by
  rw [← SixC12S0Input_merge, eval_orderedMerge, ← SixC12S0Input_left_sorted, ← SixC12S0Input_right_sorted, eval_sort, eval_sort, SixC12S0Input_flat, eval_append]
end SixCertificates
