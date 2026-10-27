import SixC42S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC42S1InputPolynomial : Polynomial := SixC42S0OutputPolynomial
theorem SixC42S1Input_merge : orderedMerge 6188 SixC42S1InputLeftSorted SixC42S1InputRightSorted = SixC42S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC42S1Input_eval (f : ℕ →* ℝ) : eval f SixC42S1InputPolynomial = eval f (expandSlices 7 3 SixC42S1InputSlices) := by
  rw [← SixC42S1Input_merge, eval_orderedMerge, ← SixC42S1Input_left_sorted, ← SixC42S1Input_right_sorted, eval_sort, eval_sort, SixC42S1Input_flat, eval_append]
end SixCertificates
