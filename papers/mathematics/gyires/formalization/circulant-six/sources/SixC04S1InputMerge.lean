import SixC04S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC04S1InputPolynomial : Polynomial := SixC04S0OutputPolynomial
theorem SixC04S1Input_merge : orderedMerge 6188 SixC04S1InputLeftSorted SixC04S1InputRightSorted = SixC04S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC04S1Input_eval (f : ℕ →* ℝ) : eval f SixC04S1InputPolynomial = eval f (expandSlices 7 13 SixC04S1InputSlices) := by
  rw [← SixC04S1Input_merge, eval_orderedMerge, ← SixC04S1Input_left_sorted, ← SixC04S1Input_right_sorted, eval_sort, eval_sort, SixC04S1Input_flat, eval_append]
end SixCertificates
