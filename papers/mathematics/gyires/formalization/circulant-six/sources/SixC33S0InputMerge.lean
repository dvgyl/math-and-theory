import SixC33S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC33S0InputPolynomial : Polynomial := rawDense
theorem SixC33S0Input_merge : orderedMerge 6188 SixC33S0InputLeftSorted SixC33S0InputRightSorted = SixC33S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC33S0Input_eval (f : ℕ →* ℝ) : eval f SixC33S0InputPolynomial = eval f (expandSlices 3 13 SixC33S0InputSlices) := by
  rw [← SixC33S0Input_merge, eval_orderedMerge, ← SixC33S0Input_left_sorted, ← SixC33S0Input_right_sorted, eval_sort, eval_sort, SixC33S0Input_flat, eval_append]
end SixCertificates
