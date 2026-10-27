import SixC14S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC14S2InputPolynomial : Polynomial := SixC14S1OutputPolynomial
theorem SixC14S2Input_merge : orderedMerge 6188 SixC14S2InputLeftSorted SixC14S2InputRightSorted = SixC14S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC14S2Input_eval (f : ℕ →* ℝ) : eval f SixC14S2InputPolynomial = eval f (expandSlices 7 11 SixC14S2InputSlices) := by
  rw [← SixC14S2Input_merge, eval_orderedMerge, ← SixC14S2Input_left_sorted, ← SixC14S2Input_right_sorted, eval_sort, eval_sort, SixC14S2Input_flat, eval_append]
end SixCertificates
