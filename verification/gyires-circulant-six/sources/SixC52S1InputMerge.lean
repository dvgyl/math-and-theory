import SixC52S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC52S1InputPolynomial : Polynomial := SixC52S0OutputPolynomial
theorem SixC52S1Input_merge : orderedMerge 6188 SixC52S1InputLeftSorted SixC52S1InputRightSorted = SixC52S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC52S1Input_eval (f : ℕ →* ℝ) : eval f SixC52S1InputPolynomial = eval f (expandSlices 5 13 SixC52S1InputSlices) := by
  rw [← SixC52S1Input_merge, eval_orderedMerge, ← SixC52S1Input_left_sorted, ← SixC52S1Input_right_sorted, eval_sort, eval_sort, SixC52S1Input_flat, eval_append]
end SixCertificates
