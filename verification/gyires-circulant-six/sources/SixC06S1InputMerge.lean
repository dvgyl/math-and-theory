import SixC06S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC06S1InputPolynomial : Polynomial := SixC06S0OutputPolynomial
theorem SixC06S1Input_merge : orderedMerge 6188 SixC06S1InputLeftSorted SixC06S1InputRightSorted = SixC06S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC06S1Input_eval (f : ℕ →* ℝ) : eval f SixC06S1InputPolynomial = eval f (expandSlices 11 5 SixC06S1InputSlices) := by
  rw [← SixC06S1Input_merge, eval_orderedMerge, ← SixC06S1Input_left_sorted, ← SixC06S1Input_right_sorted, eval_sort, eval_sort, SixC06S1Input_flat, eval_append]
end SixCertificates
