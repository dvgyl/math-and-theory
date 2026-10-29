import SixC28S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC28S2InputPolynomial : Polynomial := SixC28S1OutputPolynomial
theorem SixC28S2Input_merge : orderedMerge 6188 SixC28S2InputLeftSorted SixC28S2InputRightSorted = SixC28S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC28S2Input_eval (f : ℕ →* ℝ) : eval f SixC28S2InputPolynomial = eval f (expandSlices 13 3 SixC28S2InputSlices) := by
  rw [← SixC28S2Input_merge, eval_orderedMerge, ← SixC28S2Input_left_sorted, ← SixC28S2Input_right_sorted, eval_sort, eval_sort, SixC28S2Input_flat, eval_append]
end SixCertificates
