import SixC24S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC24S2InputPolynomial : Polynomial := SixC24S1OutputPolynomial
theorem SixC24S2Input_merge : orderedMerge 6188 SixC24S2InputLeftSorted SixC24S2InputRightSorted = SixC24S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC24S2Input_eval (f : ℕ →* ℝ) : eval f SixC24S2InputPolynomial = eval f (expandSlices 7 3 SixC24S2InputSlices) := by
  rw [← SixC24S2Input_merge, eval_orderedMerge, ← SixC24S2Input_left_sorted, ← SixC24S2Input_right_sorted, eval_sort, eval_sort, SixC24S2Input_flat, eval_append]
end SixCertificates
