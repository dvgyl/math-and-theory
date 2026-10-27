import SixC30S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC30S2InputPolynomial : Polynomial := SixC30S1OutputPolynomial
theorem SixC30S2Input_merge : orderedMerge 6188 SixC30S2InputLeftSorted SixC30S2InputRightSorted = SixC30S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC30S2Input_eval (f : ℕ →* ℝ) : eval f SixC30S2InputPolynomial = eval f (expandSlices 3 7 SixC30S2InputSlices) := by
  rw [← SixC30S2Input_merge, eval_orderedMerge, ← SixC30S2Input_left_sorted, ← SixC30S2Input_right_sorted, eval_sort, eval_sort, SixC30S2Input_flat, eval_append]
end SixCertificates
