import SixC52S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC52S2InputPolynomial : Polynomial := SixC52S1OutputPolynomial
theorem SixC52S2Input_merge : orderedMerge 6188 SixC52S2InputLeftSorted SixC52S2InputRightSorted = SixC52S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC52S2Input_eval (f : ℕ →* ℝ) : eval f SixC52S2InputPolynomial = eval f (expandSlices 13 3 SixC52S2InputSlices) := by
  rw [← SixC52S2Input_merge, eval_orderedMerge, ← SixC52S2Input_left_sorted, ← SixC52S2Input_right_sorted, eval_sort, eval_sort, SixC52S2Input_flat, eval_append]
end SixCertificates
