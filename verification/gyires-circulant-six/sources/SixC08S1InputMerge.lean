import SixC08S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC08S1InputPolynomial : Polynomial := SixC08S0OutputPolynomial
theorem SixC08S1Input_merge : orderedMerge 6188 SixC08S1InputLeftSorted SixC08S1InputRightSorted = SixC08S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC08S1Input_eval (f : ℕ →* ℝ) : eval f SixC08S1InputPolynomial = eval f (expandSlices 5 11 SixC08S1InputSlices) := by
  rw [← SixC08S1Input_merge, eval_orderedMerge, ← SixC08S1Input_left_sorted, ← SixC08S1Input_right_sorted, eval_sort, eval_sort, SixC08S1Input_flat, eval_append]
end SixCertificates
