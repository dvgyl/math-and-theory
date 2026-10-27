import SixC53S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC53S2InputPolynomial : Polynomial := SixC53S1OutputPolynomial
theorem SixC53S2Input_merge : orderedMerge 6188 SixC53S2InputLeftSorted SixC53S2InputRightSorted = SixC53S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC53S2Input_eval (f : ℕ →* ℝ) : eval f SixC53S2InputPolynomial = eval f (expandSlices 13 3 SixC53S2InputSlices) := by
  rw [← SixC53S2Input_merge, eval_orderedMerge, ← SixC53S2Input_left_sorted, ← SixC53S2Input_right_sorted, eval_sort, eval_sort, SixC53S2Input_flat, eval_append]
end SixCertificates
