import SixC48S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC48S2InputPolynomial : Polynomial := SixC48S1OutputPolynomial
theorem SixC48S2Input_merge : orderedMerge 6188 SixC48S2InputLeftSorted SixC48S2InputRightSorted = SixC48S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC48S2Input_eval (f : ℕ →* ℝ) : eval f SixC48S2InputPolynomial = eval f (expandSlices 5 3 SixC48S2InputSlices) := by
  rw [← SixC48S2Input_merge, eval_orderedMerge, ← SixC48S2Input_left_sorted, ← SixC48S2Input_right_sorted, eval_sort, eval_sort, SixC48S2Input_flat, eval_append]
end SixCertificates
