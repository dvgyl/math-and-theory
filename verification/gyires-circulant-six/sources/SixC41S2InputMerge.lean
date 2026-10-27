import SixC41S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC41S2InputPolynomial : Polynomial := SixC41S1OutputPolynomial
theorem SixC41S2Input_merge : orderedMerge 6188 SixC41S2InputLeftSorted SixC41S2InputRightSorted = SixC41S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC41S2Input_eval (f : ℕ →* ℝ) : eval f SixC41S2InputPolynomial = eval f (expandSlices 13 11 SixC41S2InputSlices) := by
  rw [← SixC41S2Input_merge, eval_orderedMerge, ← SixC41S2Input_left_sorted, ← SixC41S2Input_right_sorted, eval_sort, eval_sort, SixC41S2Input_flat, eval_append]
end SixCertificates
