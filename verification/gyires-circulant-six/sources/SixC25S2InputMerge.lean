import SixC25S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC25S2InputPolynomial : Polynomial := SixC25S1OutputPolynomial
theorem SixC25S2Input_merge : orderedMerge 6188 SixC25S2InputLeftSorted SixC25S2InputRightSorted = SixC25S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC25S2Input_eval (f : ℕ →* ℝ) : eval f SixC25S2InputPolynomial = eval f (expandSlices 7 3 SixC25S2InputSlices) := by
  rw [← SixC25S2Input_merge, eval_orderedMerge, ← SixC25S2Input_left_sorted, ← SixC25S2Input_right_sorted, eval_sort, eval_sort, SixC25S2Input_flat, eval_append]
end SixCertificates
