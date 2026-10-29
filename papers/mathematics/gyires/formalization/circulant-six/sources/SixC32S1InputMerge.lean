import SixC32S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC32S1InputPolynomial : Polynomial := SixC32S0OutputPolynomial
theorem SixC32S1Input_merge : orderedMerge 6188 SixC32S1InputLeftSorted SixC32S1InputRightSorted = SixC32S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC32S1Input_eval (f : ℕ →* ℝ) : eval f SixC32S1InputPolynomial = eval f (expandSlices 3 11 SixC32S1InputSlices) := by
  rw [← SixC32S1Input_merge, eval_orderedMerge, ← SixC32S1Input_left_sorted, ← SixC32S1Input_right_sorted, eval_sort, eval_sort, SixC32S1Input_flat, eval_append]
end SixCertificates
