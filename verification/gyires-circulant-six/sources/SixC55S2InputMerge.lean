import SixC55S2InputRight
namespace SixCertificates
open MathAndTheory.Gyires.SparsePolynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
noncomputable def SixC55S2InputPolynomial : Polynomial := SixC55S1OutputPolynomial
theorem SixC55S2Input_merge : orderedMerge 6188 SixC55S2InputLeftSorted SixC55S2InputRightSorted = SixC55S2InputPolynomial := by apply same_sound; decide +kernel
theorem SixC55S2Input_eval (f : ℕ →* ℝ) : eval f SixC55S2InputPolynomial = eval f (expandSlices 3 5 SixC55S2InputSlices) := by
  rw [← SixC55S2Input_merge, eval_orderedMerge, ← SixC55S2Input_left_sorted, ← SixC55S2Input_right_sorted, eval_sort, eval_sort, SixC55S2Input_flat, eval_append]
end SixCertificates
