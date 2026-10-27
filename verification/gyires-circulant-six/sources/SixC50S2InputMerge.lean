import SixC50S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC50S2InputPolynomial : Polynomial := SixC50S1OutputPolynomial
theorem SixC50S2Input_merge : orderedMerge 6188 SixC50S2InputLeftSorted SixC50S2InputRightSorted = SixC50S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC50S2Input_eval (f : ℕ →* ℝ) : eval f SixC50S2InputPolynomial = eval f (expandSlices 11 3 SixC50S2InputSlices) := by
  rw [← SixC50S2Input_merge, eval_orderedMerge, ← SixC50S2Input_left_sorted, ← SixC50S2Input_right_sorted, eval_sort, eval_sort, SixC50S2Input_flat, eval_append]
end SixCertificates
