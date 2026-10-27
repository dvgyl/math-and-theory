import SixC03S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC03S2InputPolynomial : Polynomial := SixC03S1OutputPolynomial
theorem SixC03S2Input_merge : orderedMerge 6188 SixC03S2InputLeftSorted SixC03S2InputRightSorted = SixC03S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC03S2Input_eval (f : ℕ →* ℝ) : eval f SixC03S2InputPolynomial = eval f (expandSlices 11 5 SixC03S2InputSlices) := by
  rw [← SixC03S2Input_merge, eval_orderedMerge, ← SixC03S2Input_left_sorted, ← SixC03S2Input_right_sorted, eval_sort, eval_sort, SixC03S2Input_flat, eval_append]
end SixCertificates
