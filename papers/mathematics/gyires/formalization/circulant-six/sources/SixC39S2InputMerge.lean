import SixC39S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC39S2InputPolynomial : Polynomial := SixC39S1OutputPolynomial
theorem SixC39S2Input_merge : orderedMerge 6188 SixC39S2InputLeftSorted SixC39S2InputRightSorted = SixC39S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC39S2Input_eval (f : ℕ →* ℝ) : eval f SixC39S2InputPolynomial = eval f (expandSlices 7 11 SixC39S2InputSlices) := by
  rw [← SixC39S2Input_merge, eval_orderedMerge, ← SixC39S2Input_left_sorted, ← SixC39S2Input_right_sorted, eval_sort, eval_sort, SixC39S2Input_flat, eval_append]
end SixCertificates
