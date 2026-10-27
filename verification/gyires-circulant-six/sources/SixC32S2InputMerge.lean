import SixC32S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC32S2InputPolynomial : Polynomial := SixC32S1OutputPolynomial
theorem SixC32S2Input_merge : orderedMerge 6188 SixC32S2InputLeftSorted SixC32S2InputRightSorted = SixC32S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC32S2Input_eval (f : ℕ →* ℝ) : eval f SixC32S2InputPolynomial = eval f (expandSlices 11 7 SixC32S2InputSlices) := by
  rw [← SixC32S2Input_merge, eval_orderedMerge, ← SixC32S2Input_left_sorted, ← SixC32S2Input_right_sorted, eval_sort, eval_sort, SixC32S2Input_flat, eval_append]
end SixCertificates
