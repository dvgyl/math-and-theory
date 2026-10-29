import SixC26S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC26S2InputPolynomial : Polynomial := SixC26S1OutputPolynomial
theorem SixC26S2Input_merge : orderedMerge 6188 SixC26S2InputLeftSorted SixC26S2InputRightSorted = SixC26S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC26S2Input_eval (f : ℕ →* ℝ) : eval f SixC26S2InputPolynomial = eval f (expandSlices 11 3 SixC26S2InputSlices) := by
  rw [← SixC26S2Input_merge, eval_orderedMerge, ← SixC26S2Input_left_sorted, ← SixC26S2Input_right_sorted, eval_sort, eval_sort, SixC26S2Input_flat, eval_append]
end SixCertificates
