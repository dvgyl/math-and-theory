import SixC19S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC19S0InputPolynomial : Polynomial := rawDense
theorem SixC19S0Input_merge : orderedMerge 6188 SixC19S0InputLeftSorted SixC19S0InputRightSorted = SixC19S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC19S0Input_eval (f : ℕ →* ℝ) : eval f SixC19S0InputPolynomial = eval f (expandSlices 7 11 SixC19S0InputSlices) := by
  rw [← SixC19S0Input_merge, eval_orderedMerge, ← SixC19S0Input_left_sorted, ← SixC19S0Input_right_sorted, eval_sort, eval_sort, SixC19S0Input_flat, eval_append]
end SixCertificates
