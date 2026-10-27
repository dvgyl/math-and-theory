import SixC18S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC18S2InputPolynomial : Polynomial := SixC18S1OutputPolynomial
theorem SixC18S2Input_merge : orderedMerge 6188 SixC18S2InputLeftSorted SixC18S2InputRightSorted = SixC18S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC18S2Input_eval (f : ℕ →* ℝ) : eval f SixC18S2InputPolynomial = eval f (expandSlices 5 13 SixC18S2InputSlices) := by
  rw [← SixC18S2Input_merge, eval_orderedMerge, ← SixC18S2Input_left_sorted, ← SixC18S2Input_right_sorted, eval_sort, eval_sort, SixC18S2Input_flat, eval_append]
end SixCertificates
