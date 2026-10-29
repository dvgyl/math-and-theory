import SixC30S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC30S1InputPolynomial : Polynomial := SixC30S0OutputPolynomial
theorem SixC30S1Input_merge : orderedMerge 6188 SixC30S1InputLeftSorted SixC30S1InputRightSorted = SixC30S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC30S1Input_eval (f : ℕ →* ℝ) : eval f SixC30S1InputPolynomial = eval f (expandSlices 11 3 SixC30S1InputSlices) := by
  rw [← SixC30S1Input_merge, eval_orderedMerge, ← SixC30S1Input_left_sorted, ← SixC30S1Input_right_sorted, eval_sort, eval_sort, SixC30S1Input_flat, eval_append]
end SixCertificates
