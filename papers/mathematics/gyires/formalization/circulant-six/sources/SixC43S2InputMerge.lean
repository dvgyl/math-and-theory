import SixC43S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC43S2InputPolynomial : Polynomial := SixC43S1OutputPolynomial
theorem SixC43S2Input_merge : orderedMerge 6188 SixC43S2InputLeftSorted SixC43S2InputRightSorted = SixC43S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC43S2Input_eval (f : ℕ →* ℝ) : eval f SixC43S2InputPolynomial = eval f (expandSlices 3 13 SixC43S2InputSlices) := by
  rw [← SixC43S2Input_merge, eval_orderedMerge, ← SixC43S2Input_left_sorted, ← SixC43S2Input_right_sorted, eval_sort, eval_sort, SixC43S2Input_flat, eval_append]
end SixCertificates
