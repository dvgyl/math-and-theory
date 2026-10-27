import SixC22S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC22S1InputPolynomial : Polynomial := SixC22S0OutputPolynomial
theorem SixC22S1Input_merge : orderedMerge 6188 SixC22S1InputLeftSorted SixC22S1InputRightSorted = SixC22S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC22S1Input_eval (f : ℕ →* ℝ) : eval f SixC22S1InputPolynomial = eval f (expandSlices 5 11 SixC22S1InputSlices) := by
  rw [← SixC22S1Input_merge, eval_orderedMerge, ← SixC22S1Input_left_sorted, ← SixC22S1Input_right_sorted, eval_sort, eval_sort, SixC22S1Input_flat, eval_append]
end SixCertificates
