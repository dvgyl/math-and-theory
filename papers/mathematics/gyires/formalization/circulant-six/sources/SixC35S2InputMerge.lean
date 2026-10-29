import SixC35S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC35S2InputPolynomial : Polynomial := SixC35S1OutputPolynomial
theorem SixC35S2Input_merge : orderedMerge 6188 SixC35S2InputLeftSorted SixC35S2InputRightSorted = SixC35S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC35S2Input_eval (f : ℕ →* ℝ) : eval f SixC35S2InputPolynomial = eval f (expandSlices 13 7 SixC35S2InputSlices) := by
  rw [← SixC35S2Input_merge, eval_orderedMerge, ← SixC35S2Input_left_sorted, ← SixC35S2Input_right_sorted, eval_sort, eval_sort, SixC35S2Input_flat, eval_append]
end SixCertificates
