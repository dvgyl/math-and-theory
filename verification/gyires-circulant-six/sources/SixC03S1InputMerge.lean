import SixC03S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC03S1InputPolynomial : Polynomial := SixC03S0OutputPolynomial
theorem SixC03S1Input_merge : orderedMerge 6188 SixC03S1InputLeftSorted SixC03S1InputRightSorted = SixC03S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC03S1Input_eval (f : ℕ →* ℝ) : eval f SixC03S1InputPolynomial = eval f (expandSlices 13 11 SixC03S1InputSlices) := by
  rw [← SixC03S1Input_merge, eval_orderedMerge, ← SixC03S1Input_left_sorted, ← SixC03S1Input_right_sorted, eval_sort, eval_sort, SixC03S1Input_flat, eval_append]
end SixCertificates
