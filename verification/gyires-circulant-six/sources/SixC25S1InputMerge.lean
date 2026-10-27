import SixC25S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC25S1InputPolynomial : Polynomial := SixC25S0OutputPolynomial
theorem SixC25S1Input_merge : orderedMerge 6188 SixC25S1InputLeftSorted SixC25S1InputRightSorted = SixC25S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC25S1Input_eval (f : ℕ →* ℝ) : eval f SixC25S1InputPolynomial = eval f (expandSlices 13 7 SixC25S1InputSlices) := by
  rw [← SixC25S1Input_merge, eval_orderedMerge, ← SixC25S1Input_left_sorted, ← SixC25S1Input_right_sorted, eval_sort, eval_sort, SixC25S1Input_flat, eval_append]
end SixCertificates
