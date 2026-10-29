import SixC53S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC53S1InputPolynomial : Polynomial := SixC53S0OutputPolynomial
theorem SixC53S1Input_merge : orderedMerge 6188 SixC53S1InputLeftSorted SixC53S1InputRightSorted = SixC53S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC53S1Input_eval (f : ℕ →* ℝ) : eval f SixC53S1InputPolynomial = eval f (expandSlices 11 13 SixC53S1InputSlices) := by
  rw [← SixC53S1Input_merge, eval_orderedMerge, ← SixC53S1Input_left_sorted, ← SixC53S1Input_right_sorted, eval_sort, eval_sort, SixC53S1Input_flat, eval_append]
end SixCertificates
