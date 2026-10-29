import SixC07S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC07S1InputPolynomial : Polynomial := SixC07S0OutputPolynomial
theorem SixC07S1Input_merge : orderedMerge 6188 SixC07S1InputLeftSorted SixC07S1InputRightSorted = SixC07S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC07S1Input_eval (f : ℕ →* ℝ) : eval f SixC07S1InputPolynomial = eval f (expandSlices 13 5 SixC07S1InputSlices) := by
  rw [← SixC07S1Input_merge, eval_orderedMerge, ← SixC07S1Input_left_sorted, ← SixC07S1Input_right_sorted, eval_sort, eval_sort, SixC07S1Input_flat, eval_append]
end SixCertificates
