import SixC27S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC27S2InputPolynomial : Polynomial := SixC27S1OutputPolynomial
theorem SixC27S2Input_merge : orderedMerge 6188 SixC27S2InputLeftSorted SixC27S2InputRightSorted = SixC27S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC27S2Input_eval (f : ℕ →* ℝ) : eval f SixC27S2InputPolynomial = eval f (expandSlices 11 3 SixC27S2InputSlices) := by
  rw [← SixC27S2Input_merge, eval_orderedMerge, ← SixC27S2Input_left_sorted, ← SixC27S2Input_right_sorted, eval_sort, eval_sort, SixC27S2Input_flat, eval_append]
end SixCertificates
