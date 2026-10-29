import SixC31S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC31S1InputPolynomial : Polynomial := SixC31S0OutputPolynomial
theorem SixC31S1Input_merge : orderedMerge 6188 SixC31S1InputLeftSorted SixC31S1InputRightSorted = SixC31S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC31S1Input_eval (f : ℕ →* ℝ) : eval f SixC31S1InputPolynomial = eval f (expandSlices 13 3 SixC31S1InputSlices) := by
  rw [← SixC31S1Input_merge, eval_orderedMerge, ← SixC31S1Input_left_sorted, ← SixC31S1Input_right_sorted, eval_sort, eval_sort, SixC31S1Input_flat, eval_append]
end SixCertificates
