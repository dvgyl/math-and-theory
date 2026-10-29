import SixC49S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC49S0InputPolynomial : Polynomial := rawDense
theorem SixC49S0Input_merge : orderedMerge 6188 SixC49S0InputLeftSorted SixC49S0InputRightSorted = SixC49S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC49S0Input_eval (f : ℕ →* ℝ) : eval f SixC49S0InputPolynomial = eval f (expandSlices 11 13 SixC49S0InputSlices) := by
  rw [← SixC49S0Input_merge, eval_orderedMerge, ← SixC49S0Input_left_sorted, ← SixC49S0Input_right_sorted, eval_sort, eval_sort, SixC49S0Input_flat, eval_append]
end SixCertificates
