import SixC50S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC50S1InputPolynomial : Polynomial := SixC50S0OutputPolynomial
theorem SixC50S1Input_merge : orderedMerge 6188 SixC50S1InputLeftSorted SixC50S1InputRightSorted = SixC50S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC50S1Input_eval (f : ℕ →* ℝ) : eval f SixC50S1InputPolynomial = eval f (expandSlices 5 11 SixC50S1InputSlices) := by
  rw [← SixC50S1Input_merge, eval_orderedMerge, ← SixC50S1Input_left_sorted, ← SixC50S1Input_right_sorted, eval_sort, eval_sort, SixC50S1Input_flat, eval_append]
end SixCertificates
