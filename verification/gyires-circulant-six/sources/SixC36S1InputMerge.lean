import SixC36S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC36S1InputPolynomial : Polynomial := SixC36S0OutputPolynomial
theorem SixC36S1Input_merge : orderedMerge 6188 SixC36S1InputLeftSorted SixC36S1InputRightSorted = SixC36S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC36S1Input_eval (f : ℕ →* ℝ) : eval f SixC36S1InputPolynomial = eval f (expandSlices 7 3 SixC36S1InputSlices) := by
  rw [← SixC36S1Input_merge, eval_orderedMerge, ← SixC36S1Input_left_sorted, ← SixC36S1Input_right_sorted, eval_sort, eval_sort, SixC36S1Input_flat, eval_append]
end SixCertificates
