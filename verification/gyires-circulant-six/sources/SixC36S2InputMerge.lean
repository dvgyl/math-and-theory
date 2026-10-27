import SixC36S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC36S2InputPolynomial : Polynomial := SixC36S1OutputPolynomial
theorem SixC36S2Input_merge : orderedMerge 6188 SixC36S2InputLeftSorted SixC36S2InputRightSorted = SixC36S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC36S2Input_eval (f : ℕ →* ℝ) : eval f SixC36S2InputPolynomial = eval f (expandSlices 3 11 SixC36S2InputSlices) := by
  rw [← SixC36S2Input_merge, eval_orderedMerge, ← SixC36S2Input_left_sorted, ← SixC36S2Input_right_sorted, eval_sort, eval_sort, SixC36S2Input_flat, eval_append]
end SixCertificates
