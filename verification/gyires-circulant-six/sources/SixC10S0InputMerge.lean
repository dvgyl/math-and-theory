import SixC10S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC10S0InputPolynomial : Polynomial := rawDense
theorem SixC10S0Input_merge : orderedMerge 6188 SixC10S0InputLeftSorted SixC10S0InputRightSorted = SixC10S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC10S0Input_eval (f : ℕ →* ℝ) : eval f SixC10S0InputPolynomial = eval f (expandSlices 11 5 SixC10S0InputSlices) := by
  rw [← SixC10S0Input_merge, eval_orderedMerge, ← SixC10S0Input_left_sorted, ← SixC10S0Input_right_sorted, eval_sort, eval_sort, SixC10S0Input_flat, eval_append]
end SixCertificates
