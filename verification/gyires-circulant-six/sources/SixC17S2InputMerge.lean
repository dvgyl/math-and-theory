import SixC17S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC17S2InputPolynomial : Polynomial := SixC17S1OutputPolynomial
theorem SixC17S2Input_merge : orderedMerge 6188 SixC17S2InputLeftSorted SixC17S2InputRightSorted = SixC17S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC17S2Input_eval (f : ℕ →* ℝ) : eval f SixC17S2InputPolynomial = eval f (expandSlices 13 11 SixC17S2InputSlices) := by
  rw [← SixC17S2Input_merge, eval_orderedMerge, ← SixC17S2Input_left_sorted, ← SixC17S2Input_right_sorted, eval_sort, eval_sort, SixC17S2Input_flat, eval_append]
end SixCertificates
