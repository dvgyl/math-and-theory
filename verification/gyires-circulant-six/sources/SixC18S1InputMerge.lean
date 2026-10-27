import SixC18S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC18S1InputPolynomial : Polynomial := SixC18S0OutputPolynomial
theorem SixC18S1Input_merge : orderedMerge 6188 SixC18S1InputLeftSorted SixC18S1InputRightSorted = SixC18S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC18S1Input_eval (f : ℕ →* ℝ) : eval f SixC18S1InputPolynomial = eval f (expandSlices 7 5 SixC18S1InputSlices) := by
  rw [← SixC18S1Input_merge, eval_orderedMerge, ← SixC18S1Input_left_sorted, ← SixC18S1Input_right_sorted, eval_sort, eval_sort, SixC18S1Input_flat, eval_append]
end SixCertificates
