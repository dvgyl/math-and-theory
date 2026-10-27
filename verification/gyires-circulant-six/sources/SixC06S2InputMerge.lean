import SixC06S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC06S2InputPolynomial : Polynomial := SixC06S1OutputPolynomial
theorem SixC06S2Input_merge : orderedMerge 6188 SixC06S2InputLeftSorted SixC06S2InputRightSorted = SixC06S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC06S2Input_eval (f : ℕ →* ℝ) : eval f SixC06S2InputPolynomial = eval f (expandSlices 5 7 SixC06S2InputSlices) := by
  rw [← SixC06S2Input_merge, eval_orderedMerge, ← SixC06S2Input_left_sorted, ← SixC06S2Input_right_sorted, eval_sort, eval_sort, SixC06S2Input_flat, eval_append]
end SixCertificates
