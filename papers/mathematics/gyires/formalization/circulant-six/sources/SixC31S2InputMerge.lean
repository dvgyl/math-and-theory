import SixC31S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC31S2InputPolynomial : Polynomial := SixC31S1OutputPolynomial
theorem SixC31S2Input_merge : orderedMerge 6188 SixC31S2InputLeftSorted SixC31S2InputRightSorted = SixC31S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC31S2Input_eval (f : ℕ →* ℝ) : eval f SixC31S2InputPolynomial = eval f (expandSlices 3 7 SixC31S2InputSlices) := by
  rw [← SixC31S2Input_merge, eval_orderedMerge, ← SixC31S2Input_left_sorted, ← SixC31S2Input_right_sorted, eval_sort, eval_sort, SixC31S2Input_flat, eval_append]
end SixCertificates
