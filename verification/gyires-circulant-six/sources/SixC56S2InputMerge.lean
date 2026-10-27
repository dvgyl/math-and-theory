import SixC56S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC56S2InputPolynomial : Polynomial := SixC56S1OutputPolynomial
theorem SixC56S2Input_merge : orderedMerge 6188 SixC56S2InputLeftSorted SixC56S2InputRightSorted = SixC56S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC56S2Input_eval (f : ℕ →* ℝ) : eval f SixC56S2InputPolynomial = eval f (expandSlices 11 5 SixC56S2InputSlices) := by
  rw [← SixC56S2Input_merge, eval_orderedMerge, ← SixC56S2Input_left_sorted, ← SixC56S2Input_right_sorted, eval_sort, eval_sort, SixC56S2Input_flat, eval_append]
end SixCertificates
