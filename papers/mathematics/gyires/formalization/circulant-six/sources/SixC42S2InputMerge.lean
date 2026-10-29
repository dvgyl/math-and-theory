import SixC42S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC42S2InputPolynomial : Polynomial := SixC42S1OutputPolynomial
theorem SixC42S2Input_merge : orderedMerge 6188 SixC42S2InputLeftSorted SixC42S2InputRightSorted = SixC42S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC42S2Input_eval (f : ℕ →* ℝ) : eval f SixC42S2InputPolynomial = eval f (expandSlices 3 13 SixC42S2InputSlices) := by
  rw [← SixC42S2Input_merge, eval_orderedMerge, ← SixC42S2Input_left_sorted, ← SixC42S2Input_right_sorted, eval_sort, eval_sort, SixC42S2Input_flat, eval_append]
end SixCertificates
