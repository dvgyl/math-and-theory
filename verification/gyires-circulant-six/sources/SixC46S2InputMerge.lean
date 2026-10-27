import SixC46S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC46S2InputPolynomial : Polynomial := SixC46S1OutputPolynomial
theorem SixC46S2Input_merge : orderedMerge 6188 SixC46S2InputLeftSorted SixC46S2InputRightSorted = SixC46S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC46S2Input_eval (f : ℕ →* ℝ) : eval f SixC46S2InputPolynomial = eval f (expandSlices 11 13 SixC46S2InputSlices) := by
  rw [← SixC46S2Input_merge, eval_orderedMerge, ← SixC46S2Input_left_sorted, ← SixC46S2Input_right_sorted, eval_sort, eval_sort, SixC46S2Input_flat, eval_append]
end SixCertificates
