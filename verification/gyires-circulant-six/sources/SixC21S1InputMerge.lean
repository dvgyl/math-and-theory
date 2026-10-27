import SixC21S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC21S1InputPolynomial : Polynomial := SixC21S0OutputPolynomial
theorem SixC21S1Input_merge : orderedMerge 6188 SixC21S1InputLeftSorted SixC21S1InputRightSorted = SixC21S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC21S1Input_eval (f : ℕ →* ℝ) : eval f SixC21S1InputPolynomial = eval f (expandSlices 11 7 SixC21S1InputSlices) := by
  rw [← SixC21S1Input_merge, eval_orderedMerge, ← SixC21S1Input_left_sorted, ← SixC21S1Input_right_sorted, eval_sort, eval_sort, SixC21S1Input_flat, eval_append]
end SixCertificates
