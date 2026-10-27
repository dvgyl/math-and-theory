import SixC59S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC59S2InputPolynomial : Polynomial := SixC59S1OutputPolynomial
theorem SixC59S2Input_merge : orderedMerge 6188 SixC59S2InputLeftSorted SixC59S2InputRightSorted = SixC59S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC59S2Input_eval (f : ℕ →* ℝ) : eval f SixC59S2InputPolynomial = eval f (expandSlices 13 5 SixC59S2InputSlices) := by
  rw [← SixC59S2Input_merge, eval_orderedMerge, ← SixC59S2Input_left_sorted, ← SixC59S2Input_right_sorted, eval_sort, eval_sort, SixC59S2Input_flat, eval_append]
end SixCertificates
