import SixC04S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC04S2InputPolynomial : Polynomial := SixC04S1OutputPolynomial
theorem SixC04S2Input_merge : orderedMerge 6188 SixC04S2InputLeftSorted SixC04S2InputRightSorted = SixC04S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC04S2Input_eval (f : ℕ →* ℝ) : eval f SixC04S2InputPolynomial = eval f (expandSlices 13 5 SixC04S2InputSlices) := by
  rw [← SixC04S2Input_merge, eval_orderedMerge, ← SixC04S2Input_left_sorted, ← SixC04S2Input_right_sorted, eval_sort, eval_sort, SixC04S2Input_flat, eval_append]
end SixCertificates
