import SixC44S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC44S1InputPolynomial : Polynomial := SixC44S0OutputPolynomial
theorem SixC44S1Input_merge : orderedMerge 6188 SixC44S1InputLeftSorted SixC44S1InputRightSorted = SixC44S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC44S1Input_eval (f : ℕ →* ℝ) : eval f SixC44S1InputPolynomial = eval f (expandSlices 3 7 SixC44S1InputSlices) := by
  rw [← SixC44S1Input_merge, eval_orderedMerge, ← SixC44S1Input_left_sorted, ← SixC44S1Input_right_sorted, eval_sort, eval_sort, SixC44S1Input_flat, eval_append]
end SixCertificates
