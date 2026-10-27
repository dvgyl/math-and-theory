import SixC22S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC22S2InputPolynomial : Polynomial := SixC22S1OutputPolynomial
theorem SixC22S2Input_merge : orderedMerge 6188 SixC22S2InputLeftSorted SixC22S2InputRightSorted = SixC22S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC22S2Input_eval (f : ℕ →* ℝ) : eval f SixC22S2InputPolynomial = eval f (expandSlices 11 13 SixC22S2InputSlices) := by
  rw [← SixC22S2Input_merge, eval_orderedMerge, ← SixC22S2Input_left_sorted, ← SixC22S2Input_right_sorted, eval_sort, eval_sort, SixC22S2Input_flat, eval_append]
end SixCertificates
