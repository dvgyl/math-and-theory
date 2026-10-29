import SixC07S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC07S2InputPolynomial : Polynomial := SixC07S1OutputPolynomial
theorem SixC07S2Input_merge : orderedMerge 6188 SixC07S2InputLeftSorted SixC07S2InputRightSorted = SixC07S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC07S2Input_eval (f : ℕ →* ℝ) : eval f SixC07S2InputPolynomial = eval f (expandSlices 5 7 SixC07S2InputSlices) := by
  rw [← SixC07S2Input_merge, eval_orderedMerge, ← SixC07S2Input_left_sorted, ← SixC07S2Input_right_sorted, eval_sort, eval_sort, SixC07S2Input_flat, eval_append]
end SixCertificates
