import SixC45S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC45S2InputPolynomial : Polynomial := SixC45S1OutputPolynomial
theorem SixC45S2Input_merge : orderedMerge 6188 SixC45S2InputLeftSorted SixC45S2InputRightSorted = SixC45S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC45S2Input_eval (f : ℕ →* ℝ) : eval f SixC45S2InputPolynomial = eval f (expandSlices 7 13 SixC45S2InputSlices) := by
  rw [← SixC45S2Input_merge, eval_orderedMerge, ← SixC45S2Input_left_sorted, ← SixC45S2Input_right_sorted, eval_sort, eval_sort, SixC45S2Input_flat, eval_append]
end SixCertificates
