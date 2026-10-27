import SixC58S0InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC58S0InputPolynomial : Polynomial := rawDense
theorem SixC58S0Input_merge : orderedMerge 6188 SixC58S0InputLeftSorted SixC58S0InputRightSorted = SixC58S0InputPolynomial := by apply same_sound; decide +kernel
theorem SixC58S0Input_eval (f : ℕ →* ℝ) : eval f SixC58S0InputPolynomial = eval f (expandSlices 11 3 SixC58S0InputSlices) := by
  rw [← SixC58S0Input_merge, eval_orderedMerge, ← SixC58S0Input_left_sorted, ← SixC58S0Input_right_sorted, eval_sort, eval_sort, SixC58S0Input_flat, eval_append]
end SixCertificates
