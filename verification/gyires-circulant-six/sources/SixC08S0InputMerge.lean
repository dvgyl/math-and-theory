import SixC08S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC08S0InputPolynomial : Polynomial := rawDense
theorem SixC08S0Input_merge : orderedMerge 6188 SixC08S0InputLeftSorted SixC08S0InputRightSorted = SixC08S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC08S0Input_eval (f : ℕ →* ℝ) : eval f SixC08S0InputPolynomial = eval f (expandSlices 13 5 SixC08S0InputSlices) := by
  rw [← SixC08S0Input_merge, eval_orderedMerge, ← SixC08S0Input_left_sorted, ← SixC08S0Input_right_sorted, eval_sort, eval_sort, SixC08S0Input_flat, eval_append]
end SixCertificates
