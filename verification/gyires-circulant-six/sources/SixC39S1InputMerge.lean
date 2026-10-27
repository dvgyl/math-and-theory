import SixC39S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC39S1InputPolynomial : Polynomial := SixC39S0OutputPolynomial
theorem SixC39S1Input_merge : orderedMerge 6188 SixC39S1InputLeftSorted SixC39S1InputRightSorted = SixC39S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC39S1Input_eval (f : ℕ →* ℝ) : eval f SixC39S1InputPolynomial = eval f (expandSlices 13 7 SixC39S1InputSlices) := by
  rw [← SixC39S1Input_merge, eval_orderedMerge, ← SixC39S1Input_left_sorted, ← SixC39S1Input_right_sorted, eval_sort, eval_sort, SixC39S1Input_flat, eval_append]
end SixCertificates
