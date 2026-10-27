import SixC15S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC15S2InputPolynomial : Polynomial := SixC15S1OutputPolynomial
theorem SixC15S2Input_merge : orderedMerge 6188 SixC15S2InputLeftSorted SixC15S2InputRightSorted = SixC15S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC15S2Input_eval (f : ℕ →* ℝ) : eval f SixC15S2InputPolynomial = eval f (expandSlices 7 11 SixC15S2InputSlices) := by
  rw [← SixC15S2Input_merge, eval_orderedMerge, ← SixC15S2Input_left_sorted, ← SixC15S2Input_right_sorted, eval_sort, eval_sort, SixC15S2Input_flat, eval_append]
end SixCertificates
