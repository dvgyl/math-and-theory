import SixC45S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC45S1InputPolynomial : Polynomial := SixC45S0OutputPolynomial
theorem SixC45S1Input_merge : orderedMerge 6188 SixC45S1InputLeftSorted SixC45S1InputRightSorted = SixC45S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC45S1Input_eval (f : ℕ →* ℝ) : eval f SixC45S1InputPolynomial = eval f (expandSlices 11 7 SixC45S1InputSlices) := by
  rw [← SixC45S1Input_merge, eval_orderedMerge, ← SixC45S1Input_left_sorted, ← SixC45S1Input_right_sorted, eval_sort, eval_sort, SixC45S1Input_flat, eval_append]
end SixCertificates
