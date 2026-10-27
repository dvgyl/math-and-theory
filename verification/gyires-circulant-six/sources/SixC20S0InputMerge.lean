import SixC20S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC20S0InputPolynomial : Polynomial := rawDense
theorem SixC20S0Input_merge : orderedMerge 6188 SixC20S0InputLeftSorted SixC20S0InputRightSorted = SixC20S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC20S0Input_eval (f : ℕ →* ℝ) : eval f SixC20S0InputPolynomial = eval f (expandSlices 11 5 SixC20S0InputSlices) := by
  rw [← SixC20S0Input_merge, eval_orderedMerge, ← SixC20S0Input_left_sorted, ← SixC20S0Input_right_sorted, eval_sort, eval_sort, SixC20S0Input_flat, eval_append]
end SixCertificates
