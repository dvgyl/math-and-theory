import SixC24S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC24S1InputPolynomial : Polynomial := SixC24S0OutputPolynomial
theorem SixC24S1Input_merge : orderedMerge 6188 SixC24S1InputLeftSorted SixC24S1InputRightSorted = SixC24S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC24S1Input_eval (f : ℕ →* ℝ) : eval f SixC24S1InputPolynomial = eval f (expandSlices 11 7 SixC24S1InputSlices) := by
  rw [← SixC24S1Input_merge, eval_orderedMerge, ← SixC24S1Input_left_sorted, ← SixC24S1Input_right_sorted, eval_sort, eval_sort, SixC24S1Input_flat, eval_append]
end SixCertificates
