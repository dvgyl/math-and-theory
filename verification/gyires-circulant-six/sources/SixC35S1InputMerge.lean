import SixC35S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC35S1InputPolynomial : Polynomial := SixC35S0OutputPolynomial
theorem SixC35S1Input_merge : orderedMerge 6188 SixC35S1InputLeftSorted SixC35S1InputRightSorted = SixC35S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC35S1Input_eval (f : ℕ →* ℝ) : eval f SixC35S1InputPolynomial = eval f (expandSlices 11 13 SixC35S1InputSlices) := by
  rw [← SixC35S1Input_merge, eval_orderedMerge, ← SixC35S1Input_left_sorted, ← SixC35S1Input_right_sorted, eval_sort, eval_sort, SixC35S1Input_flat, eval_append]
end SixCertificates
