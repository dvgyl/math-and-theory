import SixC21S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC21S2InputPolynomial : Polynomial := SixC21S1OutputPolynomial
theorem SixC21S2Input_merge : orderedMerge 6188 SixC21S2InputLeftSorted SixC21S2InputRightSorted = SixC21S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC21S2Input_eval (f : ℕ →* ℝ) : eval f SixC21S2InputPolynomial = eval f (expandSlices 7 13 SixC21S2InputSlices) := by
  rw [← SixC21S2Input_merge, eval_orderedMerge, ← SixC21S2Input_left_sorted, ← SixC21S2Input_right_sorted, eval_sort, eval_sort, SixC21S2Input_flat, eval_append]
end SixCertificates
