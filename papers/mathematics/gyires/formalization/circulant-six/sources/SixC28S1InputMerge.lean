import SixC28S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC28S1InputPolynomial : Polynomial := SixC28S0OutputPolynomial
theorem SixC28S1Input_merge : orderedMerge 6188 SixC28S1InputLeftSorted SixC28S1InputRightSorted = SixC28S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC28S1Input_eval (f : ℕ →* ℝ) : eval f SixC28S1InputPolynomial = eval f (expandSlices 7 13 SixC28S1InputSlices) := by
  rw [← SixC28S1Input_merge, eval_orderedMerge, ← SixC28S1Input_left_sorted, ← SixC28S1Input_right_sorted, eval_sort, eval_sort, SixC28S1Input_flat, eval_append]
end SixCertificates
