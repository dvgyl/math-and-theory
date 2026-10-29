import SixC41S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC41S1InputPolynomial : Polynomial := SixC41S0OutputPolynomial
theorem SixC41S1Input_merge : orderedMerge 6188 SixC41S1InputLeftSorted SixC41S1InputRightSorted = SixC41S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC41S1Input_eval (f : ℕ →* ℝ) : eval f SixC41S1InputPolynomial = eval f (expandSlices 7 13 SixC41S1InputSlices) := by
  rw [← SixC41S1Input_merge, eval_orderedMerge, ← SixC41S1Input_left_sorted, ← SixC41S1Input_right_sorted, eval_sort, eval_sort, SixC41S1Input_flat, eval_append]
end SixCertificates
