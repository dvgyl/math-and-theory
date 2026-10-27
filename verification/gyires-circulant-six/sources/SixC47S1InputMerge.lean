import SixC47S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC47S1InputPolynomial : Polynomial := SixC47S0OutputPolynomial
theorem SixC47S1Input_merge : orderedMerge 6188 SixC47S1InputLeftSorted SixC47S1InputRightSorted = SixC47S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC47S1Input_eval (f : ℕ →* ℝ) : eval f SixC47S1InputPolynomial = eval f (expandSlices 7 11 SixC47S1InputSlices) := by
  rw [← SixC47S1Input_merge, eval_orderedMerge, ← SixC47S1Input_left_sorted, ← SixC47S1Input_right_sorted, eval_sort, eval_sort, SixC47S1Input_flat, eval_append]
end SixCertificates
