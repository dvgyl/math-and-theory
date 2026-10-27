import SixC46S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC46S1InputPolynomial : Polynomial := SixC46S0OutputPolynomial
theorem SixC46S1Input_merge : orderedMerge 6188 SixC46S1InputLeftSorted SixC46S1InputRightSorted = SixC46S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC46S1Input_eval (f : ℕ →* ℝ) : eval f SixC46S1InputPolynomial = eval f (expandSlices 3 11 SixC46S1InputSlices) := by
  rw [← SixC46S1Input_merge, eval_orderedMerge, ← SixC46S1Input_left_sorted, ← SixC46S1Input_right_sorted, eval_sort, eval_sort, SixC46S1Input_flat, eval_append]
end SixCertificates
