import SixC37S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC37S2InputPolynomial : Polynomial := SixC37S1OutputPolynomial
theorem SixC37S2Input_merge : orderedMerge 6188 SixC37S2InputLeftSorted SixC37S2InputRightSorted = SixC37S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC37S2Input_eval (f : ℕ →* ℝ) : eval f SixC37S2InputPolynomial = eval f (expandSlices 3 11 SixC37S2InputSlices) := by
  rw [← SixC37S2Input_merge, eval_orderedMerge, ← SixC37S2Input_left_sorted, ← SixC37S2Input_right_sorted, eval_sort, eval_sort, SixC37S2Input_flat, eval_append]
end SixCertificates
