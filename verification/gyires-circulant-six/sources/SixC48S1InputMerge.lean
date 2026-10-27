import SixC48S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC48S1InputPolynomial : Polynomial := SixC48S0OutputPolynomial
theorem SixC48S1Input_merge : orderedMerge 6188 SixC48S1InputLeftSorted SixC48S1InputRightSorted = SixC48S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC48S1Input_eval (f : ℕ →* ℝ) : eval f SixC48S1InputPolynomial = eval f (expandSlices 11 5 SixC48S1InputSlices) := by
  rw [← SixC48S1Input_merge, eval_orderedMerge, ← SixC48S1Input_left_sorted, ← SixC48S1Input_right_sorted, eval_sort, eval_sort, SixC48S1Input_flat, eval_append]
end SixCertificates
