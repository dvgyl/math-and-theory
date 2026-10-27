import SixC54S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC54S1InputPolynomial : Polynomial := SixC54S0OutputPolynomial
theorem SixC54S1Input_merge : orderedMerge 6188 SixC54S1InputLeftSorted SixC54S1InputRightSorted = SixC54S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC54S1Input_eval (f : ℕ →* ℝ) : eval f SixC54S1InputPolynomial = eval f (expandSlices 11 3 SixC54S1InputSlices) := by
  rw [← SixC54S1Input_merge, eval_orderedMerge, ← SixC54S1Input_left_sorted, ← SixC54S1Input_right_sorted, eval_sort, eval_sort, SixC54S1Input_flat, eval_append]
end SixCertificates
