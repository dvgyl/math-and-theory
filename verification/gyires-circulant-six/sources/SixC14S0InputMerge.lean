import SixC14S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC14S0InputPolynomial : Polynomial := rawDense
theorem SixC14S0Input_merge : orderedMerge 6188 SixC14S0InputLeftSorted SixC14S0InputRightSorted = SixC14S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC14S0Input_eval (f : ℕ →* ℝ) : eval f SixC14S0InputPolynomial = eval f (expandSlices 13 5 SixC14S0InputSlices) := by
  rw [← SixC14S0Input_merge, eval_orderedMerge, ← SixC14S0Input_left_sorted, ← SixC14S0Input_right_sorted, eval_sort, eval_sort, SixC14S0Input_flat, eval_append]
end SixCertificates
