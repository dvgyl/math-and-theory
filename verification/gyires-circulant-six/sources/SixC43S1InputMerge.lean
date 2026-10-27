import SixC43S1InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC43S1InputPolynomial : Polynomial := SixC43S0OutputPolynomial
theorem SixC43S1Input_merge : orderedMerge 6188 SixC43S1InputLeftSorted SixC43S1InputRightSorted = SixC43S1InputPolynomial := by apply same_sound; decide +kernel
theorem SixC43S1Input_eval (f : ℕ →* ℝ) : eval f SixC43S1InputPolynomial = eval f (expandSlices 11 3 SixC43S1InputSlices) := by
  rw [← SixC43S1Input_merge, eval_orderedMerge, ← SixC43S1Input_left_sorted, ← SixC43S1Input_right_sorted, eval_sort, eval_sort, SixC43S1Input_flat, eval_append]
end SixCertificates
