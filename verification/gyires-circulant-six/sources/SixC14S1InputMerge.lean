import SixC14S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC14S1InputPolynomial : Polynomial := SixC14S0OutputPolynomial
theorem SixC14S1Input_merge : orderedMerge 6188 SixC14S1InputLeftSorted SixC14S1InputRightSorted = SixC14S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC14S1Input_eval (f : ℕ →* ℝ) : eval f SixC14S1InputPolynomial = eval f (expandSlices 5 7 SixC14S1InputSlices) := by
  rw [← SixC14S1Input_merge, eval_orderedMerge, ← SixC14S1Input_left_sorted, ← SixC14S1Input_right_sorted, eval_sort, eval_sort, SixC14S1Input_flat, eval_append]
end SixCertificates
