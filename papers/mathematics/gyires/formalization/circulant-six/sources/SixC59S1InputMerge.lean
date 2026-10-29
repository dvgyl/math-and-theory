import SixC59S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC59S1InputPolynomial : Polynomial := SixC59S0OutputPolynomial
theorem SixC59S1Input_merge : orderedMerge 6188 SixC59S1InputLeftSorted SixC59S1InputRightSorted = SixC59S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC59S1Input_eval (f : ℕ →* ℝ) : eval f SixC59S1InputPolynomial = eval f (expandSlices 11 13 SixC59S1InputSlices) := by
  rw [← SixC59S1Input_merge, eval_orderedMerge, ← SixC59S1Input_left_sorted, ← SixC59S1Input_right_sorted, eval_sort, eval_sort, SixC59S1Input_flat, eval_append]
end SixCertificates
