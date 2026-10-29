import SixC26S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC26S1InputPolynomial : Polynomial := SixC26S0OutputPolynomial
theorem SixC26S1Input_merge : orderedMerge 6188 SixC26S1InputLeftSorted SixC26S1InputRightSorted = SixC26S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC26S1Input_eval (f : ℕ →* ℝ) : eval f SixC26S1InputPolynomial = eval f (expandSlices 7 11 SixC26S1InputSlices) := by
  rw [← SixC26S1Input_merge, eval_orderedMerge, ← SixC26S1Input_left_sorted, ← SixC26S1Input_right_sorted, eval_sort, eval_sort, SixC26S1Input_flat, eval_append]
end SixCertificates
